//! Native transition adapters consume actual role owners. Original State proofs
//! supply readiness and output witnesses; metadata supplies identity only.
use crate::ast::*;
use crate::field_access_visitor::visit_field_accesses;
use crate::verified_field_storage_roles::Context;
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident, Pat};
use verus_syn::visit_mut::VisitMut;

#[derive(Default)]
struct Operations {
    requirements: Vec<Expr>,
    assertions: Vec<Expr>,
    bindings: Vec<(Box<Pat>,Expr)>,
    special: Vec<(Ident,SpecialOp,Option<Box<Pat>>)>,
    update: Option<(Ident,Expr)>,
}
fn collect(stmt:&TransitionStmt,out:&mut Operations)->Result<(),Error>{
    match stmt {
        TransitionStmt::Block(_,children)=>for child in children{collect(child,out)?;},
        TransitionStmt::Require(_,e)=>out.requirements.push(e.clone()),
        TransitionStmt::Assert(_,e,_)=>out.assertions.push(e.clone()),
        TransitionStmt::Update(_,field,e)=>{
            if out.update.replace((field.clone(),e.clone())).is_some(){
                return Err(Error::new(field.span(),"map-pair transition permits one variable update"));
            }
        }
        TransitionStmt::Split(span,kind,children)=>{
            match &**kind{
                SplitKind::Let(pat,_,LetKind::Normal,e)=>out.bindings.push((pat.clone(),e.clone())),
                SplitKind::Special(field,op,_,pat)=>out.special.push((field.clone(),op.clone(),pat.clone())),
                _=>return Err(Error::new(*span,"map-pair transition requires scoped lets and singleton operations")),
            }
            for child in children{collect(child,out)?;}
        }
        _=>return Err(Error::new(*stmt.get_span(),"unsupported map-pair transition statement")),
    }
    Ok(())
}
fn validate_bindings(tr:&Transition,ops:&Operations)->Result<(),Error>{
    let mut names:HashSet<_>=tr.params.iter().map(|p|p.name.to_string()).collect();
    for pat in ops.bindings.iter().map(|(pat,_)|&**pat)
        .chain(ops.special.iter().filter_map(|(_,_,pat)|pat.as_deref())){
        for name in pattern_names(pat){
            if !names.insert(name){
                return Err(Error::new(tr.name.span(),"map-pair statement bindings must not shadow transition parameters or earlier statement bindings"));
            }
        }
    }
    Ok(())
}
fn pattern_names(pat:&Pat)->HashSet<String>{
    use verus_syn::visit::Visit;
    struct Names(HashSet<String>);
    impl<'a> Visit<'a> for Names{
        fn visit_pat_ident(&mut self,p:&'a verus_syn::PatIdent){
            self.0.insert(p.ident.to_string());
            verus_syn::visit::visit_pat_ident(self,p);
        }
    }
    let mut names=Names(HashSet::new());names.visit_pat(pat);names.0
}
fn pattern_identifiers(pat:&Pat)->Vec<Ident>{
    use verus_syn::visit::Visit;
    struct Names(Vec<Ident>);
    impl<'a> Visit<'a> for Names{
        fn visit_pat_ident(&mut self,p:&'a verus_syn::PatIdent){
            self.0.push(p.ident.clone());
            verus_syn::visit::visit_pat_ident(self,p);
        }
    }
    let mut names=Names(Vec::new());names.visit_pat(pat);names.0
}
struct Inline<'a>{values:&'a HashMap<String,Expr>,shadow:HashSet<String>}
impl Inline<'_>{
    fn condition(&mut self,e:&mut Expr)->HashSet<String>{
        match e {
            Expr::Let(e)=>{
                self.visit_expr_mut(&mut e.expr);
                pattern_names(&e.pat)
            }
            Expr::Binary(e) if matches!(e.op,verus_syn::BinOp::And(_))=>{
                let left=self.condition(&mut e.left);
                let original=self.shadow.clone();self.shadow.extend(left.clone());
                let right=self.condition(&mut e.right);
                self.shadow=original;left.union(&right).cloned().collect()
            }
            _=>{self.visit_expr_mut(e);HashSet::new()}
        }
    }
}
impl VisitMut for Inline<'_>{
    fn visit_expr_mut(&mut self,e:&mut Expr){
        if let Expr::Path(p)=e {
            if p.qself.is_none()&&p.path.segments.len()==1 {
                let name=p.path.segments[0].ident.to_string();
                if !self.shadow.contains(&name) {
                    if let Some(value)=self.values.get(&name){*e=value.clone();return;}
                }
            }
        }
        verus_syn::visit_mut::visit_expr_mut(self,e);
    }
    fn visit_expr_closure_mut(&mut self,e:&mut verus_syn::ExprClosure){
        let old=self.shadow.clone();
        for input in &e.inputs{self.shadow.extend(pattern_names(&input.pat));}
        self.visit_expr_mut(&mut e.body);self.shadow=old;
    }
    fn visit_arm_mut(&mut self,arm:&mut verus_syn::Arm){
        let old=self.shadow.clone();self.shadow.extend(pattern_names(&arm.pat));
        if let Some((_,guard))=&mut arm.guard{self.visit_expr_mut(guard);}
        self.visit_expr_mut(&mut arm.body);self.shadow=old;
    }
    fn visit_block_mut(&mut self,block:&mut verus_syn::Block){
        let old=self.shadow.clone();
        for stmt in &mut block.stmts {
            self.visit_stmt_mut(stmt);
            if let verus_syn::Stmt::Local(local)=stmt{self.shadow.extend(pattern_names(&local.pat));}
        }
        self.shadow=old;
    }
    fn visit_expr_if_mut(&mut self,e:&mut verus_syn::ExprIf){
        let names=self.condition(&mut e.cond);
        let old=self.shadow.clone();self.shadow.extend(names);
        self.visit_block_mut(&mut e.then_branch);self.shadow=old;
        if let Some((_,other))=&mut e.else_branch{self.visit_expr_mut(other);}
    }
}
struct Environment<'a>{
    fields:&'a HashMap<String,Field>,
    reads:HashMap<String,Expr>,
    locals:HashMap<String,Expr>,
}
impl Environment<'_>{
    fn lower(&self,e:&Expr)->Result<Expr,Error>{
        let mut e=e.clone();let mut errors=Vec::new();
        visit_field_accesses(&mut e,|errors,field,node|{
            if let Some(value)=self.reads.get(&field.name.to_string()){*node=value.clone();}
            else{errors.push(Error::new(field.name.span(),"map-pair native operands require supplied Variable or immutable Constant observations"));}
        },&mut errors,self.fields);
        if let Some(error)=errors.into_iter().next(){return Err(error);}
        Inline{values:&self.locals,shadow:HashSet::new()}.visit_expr_mut(&mut e);Ok(e)
    }
    fn bindings(&mut self,bindings:&[(Box<Pat>,Expr)])->Result<(),Error>{
        for(pat,value)in bindings {
            let Pat::Ident(name)=&**pat else{
                return Err(Error::new(Span::call_site(),"map-pair local let requires a single scoped identifier"));
            };
            let value=self.lower(value)?;self.locals.insert(name.ident.to_string(),value);
        }
        Ok(())
    }
}
fn reserve(tokens:TokenStream,names:&mut HashSet<String>){
    for token in tokens{match token{
        TokenTree::Ident(id)=>{names.insert(id.to_string());},
        TokenTree::Group(group)=>reserve(group.stream(),names),_=>{},
    }}
}
pub fn variable_methods(sm:&SM,cx:&Context<'_>)->Result<TokenStream,Error>{
    let variable=sm.fields.iter().find(|f|matches!(f.stype,ShardableType::Variable(_))).unwrap();
    let var=&variable.name;let factory=format_ident!("field_{var}");let getter=format_ident!("value_{var}");
    let Context{types,expr,token,constants,..}=cx;
    let cn:Vec<_>=constants.iter().map(|f|&f.name).collect();
    let setters:Vec<_>=constants.iter().map(|f|format_ident!("with_{}",f.name)).collect();
    let fields:HashMap<_,_>=sm.fields.iter().map(|f|(f.name.to_string(),f.clone())).collect();
    let mut methods=Vec::new();
    for tr in &sm.transitions {
        if tr.kind!=TransitionKind::Transition{continue;}
        let mut ops=Operations::default();collect(&tr.body,&mut ops)?;
        validate_bindings(tr,&ops)?;
        if !ops.special.is_empty(){continue;}
        let Some((field,update))=&ops.update else{
            return Err(Error::new(tr.name.span(),"map-pair transition requires actual mutable or consumed ownership"));
        };
        if field!=var{return Err(Error::new(field.span(),"map-pair update must restore its Variable owner"));}
        let mut names=HashSet::new();
        let fields_ast=&sm.fields_named_ast;let generics_ast=&sm.generics;
        reserve(quote!{#fields_ast #generics_ast},&mut names);
        for t in &sm.transitions{
            names.insert(t.name.to_string());
            for p in &t.params{let n=&p.name;let ty=&p.ty;reserve(quote!{#n #ty},&mut names);}
            crate::verified_field_storage_map_pair::reserve_stmt(&t.body,&mut names);
        }
        let mut fresh=|label:&str|{
            let mut name=format!("__tsm_map_pair_{label}");
            while names.contains(&name){name.push('_');}names.insert(name.clone());
            Ident::new(&name,Span::mixed_site())
        };
        let owner=fresh("variable_owner");let slot=fresh("variable_slot");
        let owned=fresh("variable_owned");let before=fresh("variable_before");
        let state=fresh("variable_state");let frame=fresh("variable_frame");let after=fresh("variable_after");
        let raw_fn=fresh(&format!("variable_raw_{}",tr.name));
        let name=&tr.name;let req=format_ident!("{name}_requires");let enabled=format_ident!("{name}_enabled");
        let deposited=format_ident!("{name}_deposited");
        let owners=format_ident!("{name}_owners_enabled");let witness=format_ident!("{name}_witness");
        let params:Vec<_>=tr.params.iter().map(|p|{let n=&p.name;let ty=&p.ty;quote!{#n:#ty}}).collect();
        let pn:Vec<_>=tr.params.iter().map(|p|&p.name).collect();
        let mut public=Environment{fields:&fields,reads:HashMap::new(),locals:HashMap::new()};
        let mut raw=Environment{fields:&fields,reads:HashMap::new(),locals:HashMap::new()};
        let mut body=Environment{fields:&fields,reads:HashMap::new(),locals:HashMap::new()};
        public.reads.insert(var.to_string(),verus_syn::parse_quote!(old(#owner).value()));
        raw.reads.insert(var.to_string(),verus_syn::parse_quote!(old(#slot)@->Some_0.fragment().#getter()));
        body.reads.insert(var.to_string(),verus_syn::parse_quote!(#before.#getter()));
        for field in *constants{
            let n=&field.name;let read:Expr=verus_syn::parse_quote!(self.#n());
            public.reads.insert(n.to_string(),read.clone());raw.reads.insert(n.to_string(),read.clone());body.reads.insert(n.to_string(),read);
        }
        public.bindings(&ops.bindings)?;raw.bindings(&ops.bindings)?;body.bindings(&ops.bindings)?;
        let public_req:Vec<_>=ops.requirements.iter().map(|e|public.lower(e)).collect::<Result<_,_>>()?;
        let raw_req:Vec<_>=ops.requirements.iter().map(|e|raw.lower(e)).collect::<Result<_,_>>()?;
        let public_update=public.lower(update)?;let raw_update=raw.lower(update)?;let body_update=body.lower(update)?;
        let public_assert:Vec<_>=ops.assertions.iter().map(|e|public.lower(e)).collect::<Result<_,_>>()?;
        methods.push(quote!{
            proof fn #raw_fn(tracked &self,#(#params,)*tracked #slot:&mut Tracked<Option<#token>>)
                requires old(#slot)@ is Some,old(#slot)@->Some_0.loc()==self.__protocol_location(),
                    old(#slot)@->Some_0.fragment()==Fragment #expr::#factory(old(#slot)@->Some_0.fragment().#getter())
                        #(.#setters(self.#cn()))*,#(#raw_req,)*
                ensures final(#slot)@ is Some,final(#slot)@->Some_0.loc()==self.__protocol_location(),
                    final(#slot)@->Some_0.fragment()==Fragment #expr::#factory(#raw_update)#(.#setters(self.#cn()))*,
            {
                let tracked #owned=#slot.borrow_mut().tracked_take();
                let #before=#owned.fragment();
                assert(Protocol #expr::#req(#before,Fragment #expr::unit(),IMap::empty(),#(#pn),*)) by {
                    assert forall|#frame:Fragment #types,#state:State #types|
                        #state.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,Fragment #expr::unit()),#frame)==Protocol #expr::embed(#state)
                        implies State #expr::#enabled(#state,#(#pn),*)&&IMap::empty()==State #expr::#deposited(#state,#(#pn),*)&&State #expr::#owners(#state,#before,Fragment #expr::unit(),#(#pn),*) by {
                            #before.op_unit();
                            assert(#state.#var==#before.#getter());
                            #(assert(#state.#cn==self.#cn());)*
                        }
                }
                let tracked #owned=Protocol #expr::#name(#owned,#(#pn),*);
                let(#state,#after,#frame)=Protocol #expr::#witness(#before,Fragment #expr::unit(),#owned.fragment(),IMap::empty(),IMap::empty(),#(#pn),*);
                assert(#state.#var==#before.#getter());
                #(assert(#state.#cn==self.#cn());)*
                assert(#owned.fragment()==Fragment #expr::#factory(#body_update)#(.#setters(self.#cn()))*);
                *#slot=Tracked(Some(#owned));
            }
            pub proof fn #name(tracked &self,#(#params,)*tracked #owner:&mut #var #types)
                requires old(#owner).instance_id()==self.id(),#(#public_req,)*
                ensures final(#owner).instance_id()==self.id(),final(#owner).value()==(#public_update),#(#public_assert,)*
            {
                ::vstd::prelude::use_type_invariant(&*#owner);
                self.metadata.agrees(&#owner.metadata);
                Self::#raw_fn(self,#(#pn,)*&mut #owner.raw);
            }
        });
    }
    Ok(quote!{#(#methods)*})
}

/// Ordered singleton logical exchanges and one actual physical transfer. The
/// complete original transition remains the only source of State semantics.
pub fn transfer_methods(sm:&SM,cx:&Context<'_>)->Result<TokenStream,Error>{
    let variable=sm.fields.iter().find(|f|matches!(f.stype,ShardableType::Variable(_))).unwrap();
    let var=&variable.name;let var_factory=format_ident!("field_{var}");let var_getter=format_ident!("value_{var}");
    let Context{types,expr,token,constants,..}=cx;
    let cn:Vec<_>=constants.iter().map(|f|&f.name).collect();
    let setters:Vec<_>=constants.iter().map(|f|format_ident!("with_{}",f.name)).collect();
    let fields:HashMap<_,_>=sm.fields.iter().map(|f|(f.name.to_string(),f.clone())).collect();
    let mut methods=Vec::new();
    for tr in &sm.transitions {
        if tr.kind!=TransitionKind::Transition{continue;}
        let mut ops=Operations::default();collect(&tr.body,&mut ops)?;
        validate_bindings(tr,&ops)?;
        if ops.special.is_empty(){continue;}
        let mut removed=Vec::new();let mut added=Vec::new();let mut have=None;
        let mut deposit=None;let mut withdraw=None;
        for(field,op,pat)in &ops.special{
            let f=&fields[&field.to_string()];
            match (&f.stype,&op.stmt,&op.elt) {
                (ShardableType::IMap(..),MonoidStmtType::Remove,MonoidElt::SingletonKV(key,value))=>{
                    if removed.iter().any(|(other,_,_,_):&(&Field,&Expr,&Option<Box<Expr>>,&Option<Box<Pat>>)|other.name==f.name){
                        return Err(Error::new(field.span(),"map-pair exchange consumes each logical field once"));
                    }
                    removed.push((f,key,value,pat));
                }
                (ShardableType::IMap(..),MonoidStmtType::Add(false),MonoidElt::SingletonKV(key,Some(value))) if pat.is_none()=>added.push((f,key,value)),
                (ShardableType::IMap(..),MonoidStmtType::Have,MonoidElt::SingletonKV(key,Some(value))) if have.is_none()&&pat.is_none()=>have=Some((f,key,value)),
                (ShardableType::StorageIMap(_,value_type),MonoidStmtType::Deposit,MonoidElt::SingletonKV(key,Some(value))) if deposit.is_none()&&pat.is_none()=>deposit=Some((f,key,value,value_type)),
                (ShardableType::StorageIMap(_,value_type),MonoidStmtType::Withdraw,MonoidElt::SingletonKV(key,None)) if withdraw.is_none()=>withdraw=Some((f,key,pat,value_type)),
                _=>return Err(Error::new(field.span(),"map-pair transfer requires distinct logical singleton inputs and one explicit physical singleton")),
            }
        }
        if deposit.is_some()==withdraw.is_some(){return Err(Error::new(tr.name.span(),"map-pair transfer requires exactly one physical deposit or bound withdrawal"));}
        if let Some((field,_))=&ops.update{if field!=var{return Err(Error::new(field.span(),"map-pair update must restore its Variable"));}}
        if removed.is_empty()&&ops.update.is_none(){return Err(Error::new(tr.name.span(),"map-pair exchange requires actual mutable or consumed ownership"));}
        if added.len()!=removed.len()||added.iter().any(|(f,_,_)|!removed.iter().any(|(r,_,_,_)|r.name==f.name)){
            return Err(Error::new(tr.name.span(),"map-pair exchange restores each consumed logical field"));
        }
        if have.is_some_and(|(f,_,_)|removed.iter().any(|(r,_,_,_)|r.name==f.name)){
            return Err(Error::new(tr.name.span(),"map-pair readonly input must use a separate logical field"));
        }
        let mut names=HashSet::new();let field_ast=&sm.fields_named_ast;let generic_ast=&sm.generics;
        reserve(quote!{#field_ast #generic_ast},&mut names);
        for t in &sm.transitions {
            names.insert(t.name.to_string());
            for p in &t.params{let n=&p.name;let ty=&p.ty;reserve(quote!{#n #ty},&mut names);}
            crate::verified_field_storage_map_pair::reserve_stmt(&t.body,&mut names);
        }
        let mut fresh=|label:&str|{
            let mut n=format!("__tsm_map_pair_{label}");while names.contains(&n){n.push('_');}
            names.insert(n.clone());Ident::new(&n,Span::mixed_site())
        };
        let owner=fresh("transfer_variable");let slot=fresh("transfer_slot");
        let owned=fresh("transfer_owned");let before=fresh("transfer_before");
        let shared=fresh("transfer_shared");let readonly=fresh("transfer_readonly");
        let frame=fresh("transfer_frame");let pre=fresh("transfer_pre");let post=fresh("transfer_post");
        let actual=fresh("transfer_actual");let packed=fresh("transfer_packed");let dep_value=fresh("transfer_deposit_value");
        let wd=fresh("transfer_withdrawn");let unpacked=fresh("transfer_unpacked");
        let result=fresh("transfer_result");let part=fresh("transfer_part");let rest=fresh("transfer_rest");
        let raw_fn=fresh(&format!("transfer_raw_{}",tr.name));
        let inputs:Vec<_>=removed.iter().map(|(f,_,_,_)|fresh(&format!("input_{}",f.name))).collect();
        let snapshots:Vec<_>=removed.iter().map(|(f,_,_,_)|(fresh(&format!("input_{}_key",f.name)),fresh(&format!("input_{}_value",f.name)))).collect();
        let produces:Vec<_>=added.iter().map(|(f,_,_)|fresh(&format!("output_{}",f.name))).collect();
        let name=&tr.name;let req=format_ident!("{name}_requires");let enabled=format_ident!("{name}_enabled");
        let owner_req=format_ident!("{name}_owners_enabled");let deposited=format_ident!("{name}_deposited");
        let witness=format_ident!("{name}_witness");let with_shared=format_ident!("{name}_with_shared");
        let params:Vec<_>=tr.params.iter().map(|p|{let n=&p.name;let ty=&p.ty;quote!{#n:#ty}}).collect();
        let pn:Vec<_>=tr.params.iter().map(|p|&p.name).collect();
        let consumed_params:Vec<_>=removed.iter().zip(&inputs).map(|((f,_,_,_),i)|{let n=&f.name;quote!{tracked #i:#n #types,}}).collect();
        let readonly_param=have.map(|(f,_,_)|{let n=&f.name;quote!{tracked #readonly:&#n #types,}}).unwrap_or_default();
        let mut public=Environment{fields:&fields,reads:HashMap::new(),locals:HashMap::new()};
        let mut raw=Environment{fields:&fields,reads:HashMap::new(),locals:HashMap::new()};
        let mut body=Environment{fields:&fields,reads:HashMap::new(),locals:HashMap::new()};
        if ops.update.is_some(){
            public.reads.insert(var.to_string(),verus_syn::parse_quote!(old(#owner).value()));
            raw.reads.insert(var.to_string(),verus_syn::parse_quote!(old(#slot)@->Some_0.fragment().#var_getter()));
            body.reads.insert(var.to_string(),verus_syn::parse_quote!(#before.#var_getter()));
        }
        for f in *constants {
            let n=&f.name;let e:Expr=verus_syn::parse_quote!(self.#n());
            public.reads.insert(n.to_string(),e.clone());raw.reads.insert(n.to_string(),e.clone());body.reads.insert(n.to_string(),e);
        }
        public.bindings(&ops.bindings)?;raw.bindings(&ops.bindings)?;body.bindings(&ops.bindings)?;
        // Refutable logical patterns expose only ghost payload observations.
        for (((_,_,value,pat),input),(_,snapshot))in removed.iter().zip(&inputs).zip(&snapshots){
            if let Some(pat)=pat{
                for binding in pattern_identifiers(pat){
                    let e:Expr=verus_syn::parse_quote!(match #input.value(){#pat=>#binding,_=>arbitrary()});
                    public.locals.insert(binding.to_string(),e.clone());raw.locals.insert(binding.to_string(),e);
                    let e:Expr=verus_syn::parse_quote!(match #snapshot{#pat=>#binding,_=>arbitrary()});
                    body.locals.insert(binding.to_string(),e);
                }
            }
        }
        let output_count=added.len()+usize::from(withdraw.is_some());
        let output_expression=|index:usize|{
            if output_count==1{quote!{#result}}else{let index=verus_syn::Index::from(index);quote!{#result.#index@}}
        };
        if let Some((_,_,pat,_))=withdraw {
            let Some(pat)=pat else{return Err(Error::new(tr.name.span(),"physical withdrawal requires its original bound value"));};
            let Pat::Ident(binding)=&**pat else{return Err(Error::new(tr.name.span(),"physical withdrawal binding requires one payload identifier"));};
            let output=output_expression(added.len());
            public.locals.insert(binding.ident.to_string(),verus_syn::parse2(output.clone())?);
            raw.locals.insert(binding.ident.to_string(),verus_syn::parse2(output)?);
            body.locals.insert(binding.ident.to_string(),verus_syn::parse_quote!(#actual));
        }
        let mut public_req:Vec<_>=ops.requirements.iter().map(|e|public.lower(e)).collect::<Result<_,_>>()?;
        let mut raw_req:Vec<_>=ops.requirements.iter().map(|e|raw.lower(e)).collect::<Result<_,_>>()?;
        let mut public_setup=Vec::new();let mut raw_setup=Vec::new();let mut joining=Vec::new();let mut hints=Vec::new();
        for (((f,key,value,pat),input),(snap_key,snap_value))in removed.iter().zip(&inputs).zip(&snapshots){
            let n=&f.name;let key_public=public.lower(key)?;let key_raw=raw.lower(key)?;
            public_req.push(verus_syn::parse_quote!(#input.instance_id()==self.id()));
            public_req.push(verus_syn::parse_quote!(#input.key()==(#key_public)));
            raw_req.push(verus_syn::parse_quote!(#input.instance_id()==self.id()));
            raw_req.push(verus_syn::parse_quote!(#input.key()==(#key_raw)));
            if let Some(pat)=pat {
                public_req.push(verus_syn::parse_quote!(match #input.value(){#pat=>true,_=>false}));
                raw_req.push(verus_syn::parse_quote!(match #input.value(){#pat=>true,_=>false}));
            }else if let Some(value)=value {
                let vp=public.lower(value)?;let vr=raw.lower(value)?;
                public_req.push(verus_syn::parse_quote!(#input.value()==(#vp)));
                raw_req.push(verus_syn::parse_quote!(#input.value()==(#vr)));
            }else{
                return Err(Error::new(tr.name.span(),"logical removal requires an explicit value or bound pattern"));
            }
            public_setup.push(quote!{::vstd::prelude::use_type_invariant(&#input);self.metadata.agrees(&#input.metadata);});
            raw_setup.push(quote!{::vstd::prelude::use_type_invariant(&#input);self.metadata.agrees(&#input.metadata);let #snap_key=#input.key();let #snap_value=#input.value();});
            joining.push(quote!{let tracked #input=#input.raw.get().tracked_unwrap();});
        }
        // Shared observations are used without manufacturing an owned token.
        let h_fragment=if have.is_some(){quote!{#shared.fragment()}}else{quote!{Fragment #expr::unit()}};
        // Populate map hints after the common upper expression is available.
        for((f,_,_,_),(snap_key,snap_value))in removed.iter().zip(&snapshots){
            let n=&f.name;
            hints.push(quote!{::vstd::resource::tsm_collections::map_owned_frame(#before.#n,Fragment #expr::op(#h_fragment,#frame).#n,#pre.#n,#snap_key,#snap_value);});
        }
        let mut shared_setup=quote!{};
        if let Some((f,key,value))=have{
            let n=&f.name;let kp=public.lower(key)?;let vp=public.lower(value)?;
            let kr=raw.lower(key)?;let vr=raw.lower(value)?;
            public_req.push(verus_syn::parse_quote!(#readonly.instance_id()==self.id()));
            public_req.push(verus_syn::parse_quote!(#readonly.key()==(#kp)));
            public_req.push(verus_syn::parse_quote!(#readonly.value()==(#vp)));
            raw_req.push(verus_syn::parse_quote!(#readonly.instance_id()==self.id()));
            raw_req.push(verus_syn::parse_quote!(#readonly.key()==(#kr)));
            raw_req.push(verus_syn::parse_quote!(#readonly.value()==(#vr)));
            public_setup.push(quote!{::vstd::prelude::use_type_invariant(#readonly);self.metadata.agrees(&#readonly.metadata);});
            shared_setup=quote!{::vstd::prelude::use_type_invariant(#readonly);self.metadata.agrees(&#readonly.metadata);let tracked #shared=#readonly.borrow_token();};
            hints.push(quote!{
                Fragment #expr::commutative(#before,#shared.fragment());
                Fragment #expr::associative(#before,#shared.fragment(),#frame);
                Fragment #expr::associative(#shared.fragment(),#before,#frame);
                ::vstd::resource::tsm_collections::map_owned_frame(#shared.fragment().#n,Fragment #expr::op(#before,#frame).#n,#pre.#n,#readonly.key(),#readonly.value());
            });
        }
        let public_variable=if ops.update.is_some(){quote!{tracked #owner:&mut #var #types,}}else{quote!{}};
        let raw_variable=if ops.update.is_some(){quote!{tracked #slot:&mut Tracked<Option<#token>>,}}else{quote!{}};
        let variable_req=if ops.update.is_some(){quote!{
            old(#slot)@ is Some,old(#slot)@->Some_0.loc()==self.__protocol_location(),
            old(#slot)@->Some_0.fragment()==Fragment #expr::#var_factory(old(#slot)@->Some_0.fragment().#var_getter())#(.#setters(self.#cn()))*,
        }}else{quote!{}};
        let variable_public_req=if ops.update.is_some(){quote!{old(#owner).instance_id()==self.id(),}}else{quote!{}};
        let variable_public_setup=if ops.update.is_some(){quote!{::vstd::prelude::use_type_invariant(&*#owner);self.metadata.agrees(&#owner.metadata);}}else{quote!{}};
        let raw_variable_argument=if ops.update.is_some(){quote!{&mut #owner.raw,}}else{quote!{}};
        let start=if ops.update.is_some(){quote!{let tracked #owned=#slot.borrow_mut().tracked_take();}}else{
            let first=&inputs[0];quote!{let tracked #owned=#first;}
        };
        let join_start=usize::from(ops.update.is_none());
        let joins:Vec<_>=inputs.iter().skip(join_start).map(|input|quote!{let tracked #owned=#owned.join(#input);}).collect();
        let (physical_type,physical_param,physical_argument,packing)=if let Some((f,key,value,ty))=deposit{
            let key=body.lower(key)?;let vp=public.lower(value)?;let vr=raw.lower(value)?;
            public_req.push(verus_syn::parse_quote!(#actual==(#vp)));raw_req.push(verus_syn::parse_quote!(#actual==(#vr)));
            let pack=format_ident!("__carrier_pack_{}",f.name);
            (quote!{#ty},quote!{tracked #actual:#ty,},quote!{#actual,},quote!{
                let tracked mut #packed=::vstd::map::Map::tracked_empty();
                #packed.tracked_insert(#key,#actual);
                let tracked #packed=Protocol #expr::#pack(#packed);
                let #dep_value=#packed;
            })
        }else{
            let ty=withdraw.unwrap().3;(quote!{#ty},quote!{},quote!{},quote!{let #dep_value=IMap::empty();})
        };
        let public_out:Vec<_>=added.iter().enumerate().flat_map(|(i,(f,k,v))|{
            let output=output_expression(i);let key=public.lower(k);let value=public.lower(v);
            [key.map(|key|quote!{#output.key()==(#key),}),value.map(|value|quote!{#output.value()==(#value),}),Ok(quote!{#output.instance_id()==self.id(),})]
        }).collect::<Result<_,Error>>()?;
        let raw_out:Vec<_>=added.iter().enumerate().flat_map(|(i,(_,k,v))|{
            let output=output_expression(i);let key=raw.lower(k);let value=raw.lower(v);
            [key.map(|key|quote!{#output.key()==(#key),}),value.map(|value|quote!{#output.value()==(#value),}),Ok(quote!{#output.instance_id()==self.id(),})]
        }).collect::<Result<_,Error>>()?;
        let public_assert:Vec<_>=ops.assertions.iter().map(|e|public.lower(e)).collect::<Result<_,_>>()?;
        let raw_assert:Vec<_>=ops.assertions.iter().map(|e|raw.lower(e)).collect::<Result<_,_>>()?;
        let variable_post=if let Some((_,update))=&ops.update{
            let update=raw.lower(update)?;
            quote!{final(#slot)@ is Some,final(#slot)@->Some_0.loc()==self.__protocol_location(),
                final(#slot)@->Some_0.fragment()==Fragment #expr::#var_factory(#update)#(.#setters(self.#cn()))*,}
        }else{quote!{}};
        let variable_public_post=if let Some((_,update))=&ops.update{
            let update=public.lower(update)?;quote!{final(#owner).instance_id()==self.id(),final(#owner).value()==(#update),}
        }else{quote!{}};
        let return_types:Vec<_>=added.iter().map(|(f,_,_)|{let n=&f.name;quote!{#n #types}}).chain(withdraw.iter().map(|_|physical_type.clone())).collect();
        let return_type=if output_count==1{return_types[0].clone()}else{quote!{(#(Tracked<#return_types>),*)}};
        let return_decl=quote!{->(tracked #result:#return_type)};
        let dep_arg=if deposit.is_some(){quote!{#packed,}}else{quote!{}};
        let call=if have.is_some(){quote!{Protocol #expr::#with_shared(#owned,#shared,#dep_arg #(#pn),*)}}else{quote!{Protocol #expr::#name(#owned,#dep_arg #(#pn),*)}};
        let exchange=if withdraw.is_some(){quote!{let tracked(#owned,#wd)=#call;}}else{quote!{let tracked #owned=#call;let #wd=IMap::empty();}};
        let extraction=if let Some((f,key,_,_))=withdraw{
            let n=&f.name;let key=body.lower(key)?;
            let tag=format_ident!("__carrier_tag_{n}");let unpack=format_ident!("__carrier_unpack_{n}");
            let shape=format_ident!("__carrier_shape_{n}");
            quote!{
                assert(::vstd::prelude::ext_equal(#wd,Protocol #expr::#tag(IMap::empty().insert(#key,#pre.#n[#key]))));
                assert(#wd==Protocol #expr::#tag(IMap::empty().insert(#key,#pre.#n[#key])));
                Protocol #expr::#shape(IMap::empty().insert(#key,#pre.#n[#key]));
                assert(#wd.dom().finite());
                let tracked mut #unpacked=Protocol #expr::#unpack(#wd);
                let tracked #actual=#unpacked.tracked_remove(#key);
                assert(#actual==#pre.#n[#key]);
            }
        }else{quote!{}};
        let mut splits=Vec::new();let mut returns=Vec::new();
        for((f,key,value),produced)in added.iter().zip(&produces){
            let n=&f.name;let ShardableType::IMap(kt,vt)=&f.stype else{unreachable!()};
            let key=body.lower(key)?;let value=body.lower(value)?;
            let select=format_ident!("select_{n}");let without=format_ident!("without_{n}");let law=format_ident!("take_{n}_law");
            let factory=format_ident!("field_{n}");
            splits.push(quote!{
                #owned.fragment().#law();
                let #part=#owned.fragment().#select()#(.#setters(self.#cn()))*;
                let #rest=#owned.fragment().#without();
                assert(Fragment #expr::op(#part,#rest)==#owned.fragment());
                let tracked(#produced,#owned)=#owned.split(#part,#rest);
                ::vstd::resource::tsm_collections::MapFragment::<#kt,#vt>::extensionality(#produced.fragment().#n,
                    ::vstd::resource::tsm_collections::map_frag(IMap::empty().insert(#key,#value)));
                assert(#produced.fragment()==Fragment #expr::#factory(IMap::empty().insert(#key,#value))#(.#setters(self.#cn()))*);
            });
            let output=quote!{<#n #types>::__from_token(#produced,self.metadata.clone(),#key,#value)};
            returns.push(if output_count==1{output}else{quote!{Tracked(#output)}});
        }
        if withdraw.is_some(){returns.push(if output_count==1{quote!{#actual}}else{quote!{Tracked(#actual)}});}
        let return_value=if output_count==1{returns[0].clone()}else{quote!{(#(#returns),*)}};
        let restore=if let Some((_,update))=&ops.update{
            let update=body.lower(update)?;
            quote!{assert(#owned.fragment()==Fragment #expr::#var_factory(#update)#(.#setters(self.#cn()))*);*#slot=Tracked(Some(#owned));}
        }else{quote!{}};
        let variable_hint=if ops.update.is_some(){quote!{assert(#pre.#var==#before.#var_getter());}}else{quote!{}};
        let readonly_argument=if have.is_some(){quote!{#readonly,}}else{quote!{}};
        methods.push(quote!{
            proof fn #raw_fn(tracked &self,#(#params,)*#raw_variable #(#consumed_params)*#readonly_param #physical_param)#return_decl
                requires #variable_req #(#raw_req,)*
                ensures #variable_post #(#raw_out)*#(#raw_assert,)*
            {
                Fragment #expr::unit().op_unit();
                #(#raw_setup)*#shared_setup #(#joining)*#start #(#joins)*
                let #before=#owned.fragment();#packing
                assert(Protocol #expr::#req(#before,#h_fragment,#dep_value,#(#pn),*)) by {
                    assert forall|#frame:Fragment #types,#pre:State #types|
                        #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#h_fragment),#frame)==Protocol #expr::embed(#pre)
                        implies State #expr::#enabled(#pre,#(#pn),*)&&#dep_value==State #expr::#deposited(#pre,#(#pn),*)&&State #expr::#owner_req(#pre,#before,#h_fragment,#(#pn),*) by {
                            #before.op_unit();
                            Fragment #expr::associative(#before,#h_fragment,#frame);
                            #variable_hint #(assert(#pre.#cn==self.#cn());)*#(#hints)*
                        }
                }
                #exchange
                let(#pre,#post,#frame)=Protocol #expr::#witness(#before,#h_fragment,#owned.fragment(),#dep_value,#wd,#(#pn),*);
                Fragment #expr::associative(#before,#h_fragment,#frame);
                #variable_hint #(assert(#pre.#cn==self.#cn());)*
                #(#hints)*
                #extraction #(#splits)*#restore #return_value
            }
            pub proof fn #name(tracked &self,#(#params,)*#public_variable #(#consumed_params)*#readonly_param #physical_param)#return_decl
                requires #variable_public_req #(#public_req,)*
                ensures #variable_public_post #(#public_out)*#(#public_assert,)*
            {
                #variable_public_setup #(#public_setup)*
                Self::#raw_fn(self,#(#pn,)*#raw_variable_argument #(#inputs,)*#readonly_argument #physical_argument)
            }
        });
    }
    Ok(quote!{#(#methods)*})
}
