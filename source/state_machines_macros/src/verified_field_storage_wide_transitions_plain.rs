//! Actual native adapters for complete mixed-store transitions.
//! Private work in progress; every exchange uses the checked all-completion API.
use crate::ast::*;
use crate::verified_field_storage_roles::Context;
use crate::verified_field_storage_wide::{Ops, fresh, lower, role_type, role_observation};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr};

fn monoid(field:&Field,elt:&MonoidElt)->Result<Expr,Error>{
    let tokens=match elt{
        MonoidElt::General(e)=>quote!{#e},
        MonoidElt::True=>quote!{true},
        MonoidElt::OptionSome(Some(e))=>quote!{Some(#e)},
        MonoidElt::SingletonMultiset(e)=>quote!{::vstd::multiset::Multiset::singleton(#e)},
        MonoidElt::SingletonSet(e)=>quote!{::vstd::set::Set::empty().insert(#e)},
        MonoidElt::SingletonKV(k,Some(v))=>quote!{::vstd::map::Map::empty().insert(#k,#v)},
        _=>return Err(Error::new(field.name.span(),"unbound wide operand requires an explicit value")),
    };
    verus_syn::parse2(tokens)
}

fn constructor(field:&Field,elt:Option<&MonoidElt>,value:TokenStream)->TokenStream{
    match (&field.stype,elt){
        (ShardableType::Set(_)|ShardableType::PersistentSet(_),Some(MonoidElt::SingletonSet(_)))=>
            quote!{,(#value).choose()},
        (ShardableType::Multiset(_),Some(MonoidElt::SingletonMultiset(_)))=>
            quote!{,(#value).choose()},
        (ShardableType::PersistentMap(..),Some(MonoidElt::SingletonKV(_,_)))=>
            quote!{,(#value).dom().choose(),(#value)[(#value).dom().choose()]},
        (ShardableType::Option(_)|ShardableType::PersistentOption(_),_)=>quote!{,(#value)->0},
        (ShardableType::Set(_)|ShardableType::PersistentSet(_)|ShardableType::Multiset(_)
            |ShardableType::PersistentMap(..),_)=>quote!{,#value},
        _=>quote!{},
    }
}

/// The public adapter supplies exact native descriptions; the private helper
/// receives actual raw owners and borrowed raw references. Mutable public
/// invariants remain closed while the helper transfers and restores slots.
pub fn methods(sm:&SM,tr:&Transition,ops:&Ops,cx:&Context<'_>,
    carrier:&crate::verified_storage_carrier::Carrier)->Result<TokenStream,Error>{
    let zero=ops.updates.is_empty()&&!ops.special.iter().any(|(_,op)|matches!(op.stmt,MonoidStmtType::Remove));
    if !zero{return methods_with_basis(sm,tr,ops,cx,carrier,None,&tr.name);}
    let mut emitted=TokenStream::new();
    let fields:HashMap<_,_>=sm.fields.iter().map(|f|(f.name.to_string(),f.clone())).collect();
    let mut basis_reads=HashSet::new();
    for e in &ops.requires {
        crate::verified_field_storage_wide::footprint(e,&fields,&mut basis_reads)?;
    }
    for (n,op) in &ops.special {
        if matches!(op.stmt,MonoidStmtType::Have){basis_reads.insert(n.to_string());}
        match &op.elt{
            MonoidElt::General(e)|MonoidElt::SingletonSet(e)|MonoidElt::SingletonMultiset(e)
                |MonoidElt::OptionSome(Some(e))=>crate::verified_field_storage_wide::footprint(e,&fields,&mut basis_reads)?,
            MonoidElt::SingletonKV(k,v)=>{
                crate::verified_field_storage_wide::footprint(k,&fields,&mut basis_reads)?;
                if let Some(v)=v{crate::verified_field_storage_wide::footprint(v,&fields,&mut basis_reads)?;}
            },_=>{},
        }
    }
    let basis:Vec<_>=sm.fields.iter().filter(|f|
        matches!(f.stype,ShardableType::Count|ShardableType::Option(_)|ShardableType::Variable(_))
            &&!basis_reads.contains(&f.name.to_string())
    ).collect();
    if basis.is_empty(){
        return Err(Error::new(tr.name.span(),"zero ownership transition needs a mutable basis outside its read/Have footprint"));
    }
    for (index,field) in basis.iter().enumerate(){
        let native=if index==0{tr.name.clone()}else{format_ident!("{}_with_basis_{}",tr.name,field.name)};
        emitted.extend(methods_with_basis(sm,tr,ops,cx,carrier,Some(field),&native)?);
    }
    Ok(emitted)
}
fn methods_with_basis(sm:&SM,tr:&Transition,ops:&Ops,cx:&Context<'_>,
    carrier:&crate::verified_storage_carrier::Carrier,basis:Option<&Field>,native_name:&verus_syn::Ident)->Result<TokenStream,Error>{
    let types=cx.types;let expr=cx.expr;let key=&carrier.key;let stored=&carrier.value;
    let helpers=crate::verified_field_storage_properties::helpers(sm);
    let reflexive=&helpers.reflexive;let transitive=&helpers.transitive;let lift=&helpers.lift;
    let name=&tr.name;let raw_name=format_ident!("__wide_transfer_{native_name}");
    let req=format_ident!("{name}_requires");let outputs=format_ident!("{name}_outputs");
    let frame=format_ident!("{name}_frame");let witness=format_ident!("{name}_witness");
    let enabled=format_ident!("{name}_enabled");let deposited=format_ident!("{name}_deposited");
    let owners_enabled=format_ident!("{name}_owners_enabled");
    let params:Vec<_>=tr.params.iter().map(|p|{let n=&p.name;let ty=&p.ty;quote!{#n:#ty}}).collect();
    let pn:Vec<_>=tr.params.iter().map(|p|&p.name).collect();
    let fields:HashMap<_,_>=sm.fields.iter().map(|f|(f.name.to_string(),f.clone())).collect();
    let mut removed=HashMap::new();let mut added=HashMap::new();let mut have=HashMap::new();
    let mut deposits=HashMap::new();let mut withdrawals=HashMap::new();
    for (n,op) in &ops.special{
        let target=match op.stmt{
            MonoidStmtType::Remove=>&mut removed,MonoidStmtType::Add(_)=>&mut added,
            MonoidStmtType::Have=>&mut have,MonoidStmtType::Deposit=>&mut deposits,
            MonoidStmtType::Withdraw=>&mut withdrawals,
            _=>return Err(Error::new(n.span(),"unsupported wide transition operation")),
        };
        if target.insert(n.to_string(),op).is_some(){
            return Err(Error::new(n.span(),"wide transitions require one operation of each kind per field"));
        }
    }
    let mut reads=HashSet::new();
    for e in ops.requires.iter().chain(ops.updates.values()){
        crate::verified_field_storage_wide::footprint(e,&fields,&mut reads)?;
    }
    for (_,op) in &ops.special{
        match &op.elt{
            MonoidElt::General(e)|MonoidElt::SingletonSet(e)|MonoidElt::SingletonMultiset(e)
                |MonoidElt::OptionSome(Some(e))=>crate::verified_field_storage_wide::footprint(e,&fields,&mut reads)?,
            MonoidElt::SingletonKV(k,v)=>{
                crate::verified_field_storage_wide::footprint(k,&fields,&mut reads)?;
                if let Some(v)=v{crate::verified_field_storage_wide::footprint(v,&fields,&mut reads)?;}
            },
            _=>{},
        }
    }
    let mut mutable:HashSet<_>=ops.updates.keys().cloned().collect();
    // Zero additions require a real mutable basis; the first original logical
    // field is passed by the caller and restored with its original value.
    if mutable.is_empty()&&removed.is_empty(){
        let basis=basis.ok_or_else(||Error::new(name.span(),"zero ownership transition needs a real mutable basis"))?;
        mutable.insert(basis.name.to_string());
    }
    let supplied:Vec<_>=sm.fields.iter().filter(|f|{
        let n=f.name.to_string();
        mutable.contains(&n)||removed.contains_key(&n)||have.contains_key(&n)
            ||matches!(f.stype,ShardableType::Variable(_))&&reads.contains(&n)
    }).collect();
    let cn:Vec<_>=cx.constants.iter().map(|f|&f.name).collect();
    let setters:Vec<_>=cn.iter().map(|n|format_ident!("with_{n}")).collect();
    let initial=fresh(sm,tr,"native_initial");let h=fresh(sm,tr,"native_shared");
    let owned=fresh(sm,tr,"native_owned");let observation=fresh(sm,tr,"native_observation");
    let deposit=fresh(sm,tr,"native_deposit");let deposit_view=fresh(sm,tr,"native_deposit_view");
    let physical=fresh(sm,tr,"native_physical");let before=fresh(sm,tr,"native_before");
    let after=fresh(sm,tr,"native_after");let completion=fresh(sm,tr,"native_completion");
    let pair=fresh(sm,tr,"native_pair");let choices=fresh(sm,tr,"native_choices");
    let result=fresh(sm,tr,"native_result");
    let mut arguments=HashMap::new();let mut descriptions=HashMap::new();
    let mut public_inputs=vec![];let mut raw_inputs=vec![];let mut call_args=vec![];
    let mut public_pre=vec![];let mut raw_pre=vec![];let mut public_prefix=vec![];
    let mut take=vec![];let mut actual_owners=vec![];let mut observes=vec![];
    let mut observed_inputs=vec![];let mut values=HashMap::new();let mut public_values=HashMap::new();
    let mut readiness_descriptions=vec![];let mut readiness_values=vec![];
    let mut readiness_owned_shapes=vec![];
    for f in cx.constants{
        let n=&f.name;values.insert(n.to_string(),quote!{self.#n()});public_values.insert(n.to_string(),quote!{self.#n()});
    }
    for f in &supplied{
        let n=&f.name;let ns=n.to_string();let a=fresh(sm,tr,&format!("native_input_{n}"));
        let d=fresh(sm,tr,&format!("native_value_{n}"));let ty=f.get_type();
        let operand=removed.get(&ns).or_else(||have.get(&ns)).map(|op|&op.elt);
        let role=role_type(f,operand);let shape=format_ident!("field_{n}");
        let canonical=quote!{Fragment #expr::#shape(#d)#(.#setters(self.#cn()))*};
        readiness_descriptions.push(quote!{#d:#ty,});
        readiness_values.push(d.clone());
        if mutable.contains(&ns)||removed.contains_key(&ns){
            readiness_owned_shapes.push(canonical.clone());
        }
        arguments.insert(ns.clone(),a.clone());descriptions.insert(ns.clone(),d.clone());
        values.insert(ns.clone(),quote!{#d});
        let native=role_observation(f,operand,if mutable.contains(&ns){quote!{old(#a)}}else{quote!{#a}});
        public_values.insert(ns.clone(),native.clone());
        raw_inputs.push(quote!{#d:#ty,});
        call_args.push(role_observation(f,operand,quote!{#a}));
        public_pre.push(quote!{#a.instance_id()==self.id()});
        let invariant=if removed.contains_key(&ns){quote!{&#a}}else{quote!{&*#a}};
        public_prefix.push(quote!{::vstd::prelude::use_type_invariant(#invariant);self.metadata.agrees(&#a.metadata);});
        if mutable.contains(&ns){
            public_inputs.push(quote!{tracked #a:&mut #role #types,});
            raw_inputs.push(quote!{tracked #a:&mut Tracked<Option<Token #types>>,});
            raw_pre.push(quote!{old(#a)@ is Some});
            raw_pre.push(quote!{old(#a)@->Some_0.loc()==self.metadata.value().protocol_location});
            raw_pre.push(quote!{old(#a)@->Some_0.fragment()==#canonical});
            call_args.push(quote!{&mut #a.raw});
            let raw=fresh(sm,tr,&format!("native_owner_{n}"));
            if basis.is_some(){
                let saved=fresh(sm,tr,&format!("native_basis_fragment_{n}"));let restored=fresh(sm,tr,&format!("native_basis_restored_{n}"));
                let empty=fresh(sm,tr,&format!("native_basis_empty_{n}"));
                take.push(quote!{let tracked #raw=#a.borrow_mut().tracked_take();let #saved=#raw.fragment();
                    Fragment #expr::unit().op_unit();
                    let #empty=Fragment #expr::empty()#(.#setters(self.#cn()))*;
                    assert(Fragment #expr::op(#empty,#saved)==#saved);
                    let tracked(#raw,#restored)=#raw.split(#empty,#saved);*#a=Tracked(Some(#restored));});
            }else{take.push(quote!{let tracked #raw=#a.borrow_mut().tracked_take();});}actual_owners.push(raw);
        }else if removed.contains_key(&ns){
            public_inputs.push(quote!{tracked #a:#role #types,});raw_inputs.push(quote!{tracked #a:Token #types,});
            raw_pre.push(quote!{#a.loc()==self.metadata.value().protocol_location});
            raw_pre.push(quote!{#a.fragment()==#canonical});
            call_args.push(if matches!(f.stype,ShardableType::Set(_)|ShardableType::Multiset(_)|ShardableType::PersistentMap(..))
                &&matches!(operand,Some(MonoidElt::General(_))){quote!{#a.raw.get().token.tracked_unwrap()}}
                else{quote!{#a.raw.get().tracked_unwrap()}});
            actual_owners.push(a);
        }else{
            public_inputs.push(quote!{tracked #a:&#role #types,});raw_inputs.push(quote!{tracked #a:&Token #types,});
            raw_pre.push(quote!{#a.loc()==self.metadata.value().protocol_location});
            raw_pre.push(quote!{#a.fragment()==#canonical});
            call_args.push(quote!{#a.borrow_token()});
            let observed=fresh(sm,tr,&format!("native_observed_{n}"));
            observes.push(quote!{let tracked #observed=#a.observe();});observed_inputs.push((a,observed));
        }
    }
    let readiness_pre_start=raw_pre.len();
    let mut raw_bindings=vec![];let mut public_bindings=vec![];
    for (field,binding) in &ops.have_bindings{
        let f=&fields[field];let a=&arguments[field];let d=&descriptions[field];
        values.insert(binding.to_string(),match &f.stype{
            ShardableType::PersistentMap(..)=>{
                let MonoidElt::SingletonKV(k,_)=&have[field].elt else{return Err(Error::new(binding.span(),"bound Map Have requires singleton key"));};
                let key=lower(k,&fields,&values)?;raw_pre.push(quote!{#d.contains_key(#key)});
                let public_key=lower(k,&fields,&public_values)?;public_pre.push(quote!{#a.key()==#public_key});quote!{#d[#key]}
            },
            _=>quote!{#d->0},
        });
        public_values.insert(binding.to_string(),quote!{#a.value()});
        let raw_value=&values[&binding.to_string()];raw_bindings.push(quote!{let #binding=#raw_value;});
        public_bindings.push(quote!{let #binding=#a.value();});
    }
    for e in &ops.requires{
        let public=lower(e,&fields,&public_values)?;let raw=lower(e,&fields,&values)?;
        public_pre.push(quote!{{#(#public_bindings)*#public}});raw_pre.push(quote!{{#(#raw_bindings)*#raw}});
    }
    for (n,op) in removed.iter().chain(have.iter()){
        if ops.have_bindings.contains_key(n){continue}
        let native=monoid(&fields[n],&op.elt)?;
        let lhs=&values[n];let rhs=lower(&native,&fields,&values)?;
        raw_pre.push(if have.contains_key(n)&&matches!(fields[n].stype,ShardableType::Count){
            quote!{#lhs>=#rhs}
        }else{quote!{#lhs==#rhs}});
        let lhs=&public_values[n];let rhs=lower(&native,&fields,&public_values)?;
        public_pre.push(if have.contains_key(n)&&matches!(fields[n].stype,ShardableType::Count){
            quote!{#lhs>=#rhs}
        }else{quote!{#lhs==#rhs}});
    }
    let readiness_pre=raw_pre[readiness_pre_start..].to_vec();
    let mut pack=vec![];let mut actual_args=vec![];
    // Native physical arguments follow the original field order.
    for f in sm.fields.iter().filter(|f|deposits.contains_key(&f.name.to_string())){
        let n=&f.name;let a=fresh(sm,tr,&format!("native_actual_{n}"));let ty=f.get_type();
        let operand=monoid(f,&deposits[&n.to_string()].elt)?;
        public_inputs.push(quote!{tracked #a:#ty,});raw_inputs.push(quote!{tracked #a:#ty,});
        public_pre.push(quote!{#a==#operand});raw_pre.push(quote!{#a==#operand});actual_args.push(quote!{#a});
        let packed=fresh(sm,tr,&format!("native_packed_{n}"));
        pack.push(crate::verified_field_storage_wide_transfers::deposit(f,key,stored,&a,&deposit,&packed)?);
    }
    call_args.extend(actual_args);
    let first=&actual_owners[0];let joins:Vec<_>=actual_owners.iter().skip(1).map(|a|quote!{let tracked #owned=#owned.join(#a);}).collect();
    let mut observe=quote!{#(#observes)*};
    if observed_inputs.is_empty(){
        observe.extend(quote!{let #h=Fragment #expr::empty();#owned.fragment().op_unit();});
    }else{
        let first=&observed_inputs[0].1;observe.extend(quote!{
            let tracked #observation=#first;
            #reflexive::<Protocol #types>(#observation.fragment());
        });
        for (index,(_,other)) in observed_inputs.iter().enumerate().skip(1){
            let previous=fresh(sm,tr,&format!("native_upper_{index}"));
            observe.extend(quote!{let #previous=#observation.fragment();let tracked #observation=#observation.join(&#other);});
            for (prior,_) in observed_inputs.iter().take(index){
                observe.extend(quote!{
                    #transitive::<Protocol #types>(#prior.fragment(),#previous,#observation.fragment());
                });
            }
        }
    }
    let shared_fragment=if observed_inputs.is_empty(){quote!{}}else{quote!{let #h=#observation.fragment();}};
    let physical_argument=if deposits.is_empty(){quote!{}}else{quote!{#deposit,}};
    let exchange=if observed_inputs.is_empty(){
        if withdrawals.is_empty(){quote!{
            let tracked #owned=Protocol #expr::#name(#owned,#physical_argument #(#pn),*);
            let tracked #physical:IMap<#key,#stored>=IMap::tracked_empty();
        }}else{quote!{
            let tracked(#owned,#physical)=Protocol #expr::#name(#owned,#physical_argument #(#pn),*);
        }}
    }else{quote!{
        Protocol #expr::#frame(#initial,#h,#deposit_view,#(#pn),*);
        let #choices=ISet::new(|#pair:(Fragment #types,IMap<#key,#stored>)|
            Protocol #expr::#outputs(#initial,#h,#pair.0,#deposit_view,#pair.1,#(#pn),*));
        let tracked(#owned,#physical)=#owned.exchange_nondeterministic_with_observation(&#observation,#deposit,#choices);
    }};
    let mut raw_post=vec![];let mut public_post=vec![];let mut restore=vec![];
    let mut split_helpers=vec![];
    let mut extract=vec![];let mut output_types=HashMap::new();let mut output_values=HashMap::new();
    let mut binding_outputs=HashMap::new();let mut field_outputs=HashMap::new();
    let mut witness_values=HashMap::new();
    for f in &sm.fields{let n=&f.name;witness_values.insert(n.to_string(),quote!{#before.#n});}
    let binding_defs:Vec<_>=ops.bindings.iter().map(|(n,e)|{
        let e=lower(e,&fields,&witness_values)?;Ok(quote!{let #n=#e;})
    }).collect::<Result<_,Error>>()?;
    let produced:Vec<_>=sm.fields.iter().filter(|f|added.contains_key(&f.name.to_string())||withdrawals.contains_key(&f.name.to_string())).collect();
    let mut ordered_outputs:Vec<(String,Option<verus_syn::Ident>)>=vec![];
    let mut ghost_types=HashMap::new();
    let mut global_reads=HashSet::new();
    for op in withdrawals.values(){
        if let MonoidElt::SingletonKV(expression,_)=&op.elt {
            crate::verified_field_storage_wide::footprint(expression,&fields,&mut global_reads)?;
        }
    }
    let mut global_binding_defs=vec![];
    for f in &sm.fields {
        if global_reads.contains(&f.name.to_string())&&matches!(f.stype,
            ShardableType::Count|ShardableType::PersistentBool|ShardableType::PersistentOption(_)
            |ShardableType::Multiset(_)|ShardableType::Set(_)|ShardableType::PersistentSet(_)
            |ShardableType::PersistentMap(..))
        {
            let binding=fresh(sm,tr,&format!("native_global_read_{}",f.name));
            let n=&f.name;let ty=f.get_type();
            ordered_outputs.push((f.name.to_string(),Some(binding.clone())));
            ghost_types.insert(binding.to_string(),quote!{Ghost<#ty>});
            global_binding_defs.push(quote!{let #binding=#before.#n;});
        }
        for (binding,expression) in &ops.bindings {
            let mut used=HashSet::new();
            crate::verified_field_storage_wide::footprint(expression,&fields,&mut used)?;
            let physical:Vec<_>=used.iter().filter(|n|fields[*n].stype.is_storage()).collect();
            if physical.len()!=1 {
                return Err(Error::new(binding.span(),"native birds-eye result requires one physical source field"));
            }
            if physical[0]==&f.name.to_string() {
                let ty=match &f.stype {
                    ShardableType::StorageOption(ty)|ShardableType::StorageMap(_,ty)=>ty,
                    _=>unreachable!(),
                };
                ordered_outputs.push((f.name.to_string(),Some(binding.clone())));
                ghost_types.insert(binding.to_string(),quote!{Ghost<#ty>});
            }
        }
        if produced.iter().any(|out|out.name==f.name) {
            ordered_outputs.push((f.name.to_string(),None));
        }
    }
    let tuple=ordered_outputs.len()>1;
    for f in sm.fields.iter().filter(|f|mutable.contains(&f.name.to_string())||added.contains_key(&f.name.to_string())){
        let n=&f.name;let ns=n.to_string();let select=format_ident!("select_{n}");let without=format_ident!("without_{n}");
        let law=format_ident!("take_{n}_law");let part=fresh(sm,tr,&format!("native_part_{n}"));
        let rest=fresh(sm,tr,&format!("native_rest_{n}"));let raw=fresh(sm,tr,&format!("native_output_{n}"));
        let split_helper=fresh(sm,tr,&format!("native_split_helper_{native_name}_{n}"));
        let split_owner=fresh(sm,tr,&format!("native_split_owner_{n}"));
        let split_result=fresh(sm,tr,&format!("native_split_result_{n}"));
        split_helpers.push(quote!{
            proof fn #split_helper(tracked &self,tracked #split_owner:Token #types)
                ->(tracked #split_result:(Token #types,Token #types))
                requires #split_owner.fragment()==#split_owner.fragment()#(.#setters(self.#cn()))*,
                ensures #split_result.0.loc()==#split_owner.loc(),
                    #split_result.1.loc()==#split_owner.loc(),
                    #split_result.0.fragment()==#split_owner.fragment().#select()#(.#setters(self.#cn()))*,
                    #split_result.1.fragment()==#split_owner.fragment().#without(),
            {
                #split_owner.fragment().#law();
                let #part=#split_owner.fragment().#select()#(.#setters(self.#cn()))*;
                let #rest=#split_owner.fragment().#without();
                assert(Fragment #expr::op(#part,#rest)==#split_owner.fragment());
                #split_owner.split(#part,#rest)
            }
        });
        let split=quote!{let tracked(#raw,#owned)=self.#split_helper(#owned);};
        if mutable.contains(&ns){
            let a=&arguments[&ns];let factory=format_ident!("field_{n}");let d=&descriptions[&ns];
            let value=if let Some(e)=ops.updates.get(&ns){lower(e,&fields,&values)?}else{quote!{#d}};
            raw_post.push(quote!{final(#a)@ is Some});
            raw_post.push(quote!{final(#a)@->Some_0.loc()==self.metadata.value().protocol_location});
            raw_post.push(quote!{{#(#raw_bindings)*final(#a)@->Some_0.fragment()==Fragment #expr::#factory(#value)#(.#setters(self.#cn()))*}});
            public_post.push(quote!{final(#a).instance_id()==self.id()});
            let value=if let Some(e)=ops.updates.get(&ns){lower(e,&fields,&public_values)?}else{public_values[&ns].clone()};
            let access=role_observation(f,None,quote!{final(#a)});
            public_post.push(quote!{{#(#public_bindings)*#access==#value}});
            if basis.is_none(){restore.push(quote!{#split *#a=Tracked(Some(#raw));});}
        }
        if added.contains_key(&ns)&&(!mutable.contains(&ns)||basis.is_some()){
            let op=added[&ns];let role=role_type(f,Some(&op.elt));let operand=monoid(f,&op.elt)?;
            let native=lower(&operand,&fields,&witness_values)?;
            let normalization=if !removed.contains_key(&ns){
                match &f.stype{
                    ShardableType::Set(element)=>quote!{
                        ::vstd::resource::tsm_collections::Pointwise::extensionality(
                            ::vstd::resource::tsm_collections::set_frag::<#element>(ISet::empty()),
                            ::vstd::resource::tsm_collections::SetFragment::unit());
                        assert(#initial.#n==::vstd::resource::tsm_collections::SetFragment::unit());
                        ::vstd::resource::tsm_collections::set_join(ISet::empty(),(#native).to_iset());
                        assert(::vstd::prelude::ext_equal(ISet::empty().union((#native).to_iset()),(#native).to_iset()));
                        assert(#owned.fragment().#n==::vstd::resource::tsm_collections::set_frag((#native).to_iset()));
                    },
                    ShardableType::Multiset(element)=>{
                        let member=fresh(sm,tr,&format!("native_output_multiset_member_{n}"));
                        quote!{
                        assert(#initial.#n==::vstd::resource::tsm_finite_multiset::FiniteMultisetRA::unit());
                        ::vstd::resource::tsm_finite_multiset::finite_multiset_join(
                            ::vstd::multiset::Multiset::empty(),#native);
                        ::vstd::resource::tsm_finite_multiset::finite_multiset_frag(#native).op_unit();
                        assert forall|#member:#element|
                            #owned.fragment().#n.at(#member)==
                                ::vstd::resource::tsm_finite_multiset::finite_multiset_frag(#native).at(#member) by {
                            broadcast use {::vstd::multiset::group_multiset_axioms,
                                ::vstd::map::group_map_lemmas,::vstd::set::group_set_lemmas};
                        };
                        ::vstd::resource::tsm_finite_multiset::FiniteMultisetRA::extensionality(
                            #owned.fragment().#n,::vstd::resource::tsm_finite_multiset::finite_multiset_frag(#native));
                        assert(#owned.fragment().#n==::vstd::resource::tsm_finite_multiset::finite_multiset_frag(#native));
                    }},
                    _=>quote!{},
                }
            }else{quote!{}};
            let ctor=constructor(f,Some(&op.elt),native);
            extract.push(quote!{#normalization #split let tracked #raw=<#role #types>::__from_token(#raw,self.metadata.clone()#ctor);});
            output_types.insert(ns.clone(),if tuple{quote!{Tracked<#role #types>}}else{quote!{#role #types}});
            output_values.insert(ns.clone(),if tuple{quote!{Tracked(#raw)}}else{quote!{#raw}});
        }
    }
    for f in &produced{
        let n=&f.name;let ns=n.to_string();
        if withdrawals.contains_key(&ns){
            let native=fresh(sm,tr,&format!("native_withdrawn_{n}"));let selected=fresh(sm,tr,&format!("native_selection_{n}"));
            // The actual output is the per-field physical delta of the SAME
            // checked before/after witness used for logical output selection.
            let native_witness=match &f.stype{
                ShardableType::StorageOption(_)=>quote!{#before.#n},
                ShardableType::StorageMap(..)=>quote!{#before.#n.remove_keys(#after.#n.dom())},
                _=>unreachable!(),
            };
            let expected=fresh(sm,tr,&format!("native_selection_expected_{n}"));
            extract.push(crate::verified_field_storage_wide_transfers::withdraw(f,key,stored,&physical,native_witness,&expected,&selected,&native)?);
            let payload=fresh(sm,tr,&format!("native_payload_{n}"));
            let ty=match &f.stype{
                ShardableType::StorageOption(ty)=>{
                    if ops.withdrawals.contains_key(&ns) {
                        extract.push(quote!{let tracked #payload=#native.tracked_unwrap();});quote!{#ty}
                    }else{
                        extract.push(quote!{let tracked #payload=#native;});quote!{Option<#ty>}
                    }
                },
                ShardableType::StorageMap(_,ty)=>{
                    let MonoidElt::SingletonKV(original_key,_)=&withdrawals[&ns].elt else{
                        return Err(Error::new(n.span(),"native physical withdrawal currently requires singleton key"));
                    };
                    let original_key=lower(original_key,&fields,&witness_values)?;
                    let ShardableType::StorageMap(native_key,_) = &f.stype else{unreachable!()};
                    let element=fresh(sm,tr,&format!("native_withdrawal_extensional_key_{n}"));
                    // Unpacking preserves the actual map's IMap image. Normalize
                    // its finite Map identity against the SAME Strong witness
                    // before extracting the original singleton withdrawal key.
                    extract.push(quote!{
                        let #expected=#before.#n.remove_keys(#after.#n.dom());
                        assert(#native.to_imap()==#expected.to_imap());
                        assert forall|#element:#native_key|
                            #[trigger] #native.contains_key(#element)==#expected.contains_key(#element) by {
                            assert(#native.to_imap().contains_key(#element)==#expected.to_imap().contains_key(#element));
                        }
                        assert forall|#element:#native_key| #[trigger] #native.contains_key(#element)
                            implies #native[#element]==#expected[#element] by {
                            assert(#native.to_imap()[#element]==#expected.to_imap()[#element]);
                        }
                        assert(::vstd::prelude::ext_equal(#native,#expected));
                        assert(#native==#expected);
                        assert(#expected.contains_key(#original_key));
                        assert(#expected[#original_key]==#before.#n[#original_key]);
                        let tracked mut #native=#native;
                        let tracked #payload=#native.tracked_remove(#original_key);
                        assert(#payload==#before.#n[#original_key]);
                    });quote!{#ty}
                },_=>unreachable!(),
            };
            output_types.insert(ns.clone(),if tuple{quote!{Tracked<#ty>}}else{quote!{#ty}});
            output_values.insert(ns.clone(),if tuple{quote!{Tracked(#payload)}}else{quote!{#payload}});
        }
    }
    let outtypes:Vec<_>=ordered_outputs.iter().map(|(field,binding)|
        if let Some(binding)=binding{ghost_types[&binding.to_string()].clone()}else{output_types[field].clone()}
    ).collect();
    let outvalues:Vec<_>=ordered_outputs.iter().map(|(field,binding)|
        if let Some(binding)=binding{quote!{Ghost(#binding)}}else{output_values[field].clone()}
    ).collect();
    let mut ghost_outputs=HashMap::new();
    for (index,(ns,binding)) in ordered_outputs.iter().enumerate(){
        let ix=verus_syn::Index::from(index);
        let access=if tuple{quote!{#result.#ix@}}else{quote!{#result}};
        if let Some(binding)=binding{
            ghost_outputs.insert(binding.to_string(),access);
            continue;
        }
        let f=&fields[ns];
        field_outputs.insert(ns.clone(),access.clone());
        if let Some(binding)=ops.withdrawals.get(ns){binding_outputs.insert(binding.to_string(),access.clone());}
        if let Some(op)=added.get(ns){
            raw_post.push(quote!{#access.instance_id()==self.id()});public_post.push(quote!{#access.instance_id()==self.id()});
            let actual=role_observation(f,Some(&op.elt),access);
            if let Ok(value)=lower(&monoid(f,&op.elt)?,&fields,&values){raw_post.push(quote!{#actual==#value});}
            if let Ok(value)=lower(&monoid(f,&op.elt)?,&fields,&public_values){public_post.push(quote!{#actual==#value});}
        }
    }
    let mut result_bindings=vec![];
    for (binding,expression) in &ops.bindings{
        if let Some(output)=ghost_outputs.get(&binding.to_string()){
            result_bindings.push(quote!{let #binding=#output;});
            let mut used=HashSet::new();
            crate::verified_field_storage_wide::footprint(expression,&fields,&mut used)?;
            for n in used.iter().filter(|n|withdrawals.contains_key(*n)) {
                let actual=&field_outputs[n];
                let relation=if matches!(fields[n].stype,ShardableType::StorageOption(_))
                    &&!ops.withdrawals.contains_key(n) {
                    quote!{#actual==Some(#binding)}
                }else{quote!{#actual==#binding}};
                raw_post.push(relation.clone());public_post.push(relation);
            }
            continue;
        }
        let mut used=HashSet::new();crate::verified_field_storage_wide::footprint(expression,&fields,&mut used)?;
        let storage=used.iter().find(|n|fields[*n].stype.is_storage());
        let binding_value=if let Some(storage)=storage{
            if let Some(output)=field_outputs.get(storage){output.clone()}
            else{
                let produced_bag=produced.iter().find(|f|matches!(f.stype,ShardableType::Multiset(_)))
                    .ok_or_else(||Error::new(binding.span(),"physical selected binder needs an actual logical or physical output"))?;
                let output=&field_outputs[&produced_bag.name.to_string()];quote!{#output.multiset().choose()}
            }
        }else{lower(expression,&fields,&public_values)?};
        result_bindings.push(quote!{let #binding=#binding_value;});
    }
    let mut raw_assert_values=values.clone();raw_assert_values.extend(binding_outputs.clone());
    let mut public_assert_values=public_values.clone();public_assert_values.extend(binding_outputs.clone());
    for e in &ops.asserts{
        if let Ok(assertion)=lower(e,&fields,&raw_assert_values){raw_post.push(assertion);}
        if let Ok(assertion)=lower(e,&fields,&public_assert_values){public_post.push(assertion);}
    }
    let raw_binding_defs:Vec<_>=binding_outputs.iter().map(|(n,v)|{let n=format_ident!("{n}");quote!{let #n=#v;}}).collect();
    raw_post=raw_post.into_iter().map(|fact|quote!{{#(#raw_bindings)*#(#raw_binding_defs)*#(#result_bindings)*#fact}}).collect();
    public_post=public_post.into_iter().map(|fact|quote!{{#(#public_bindings)*#(#raw_binding_defs)*#(#result_bindings)*#fact}}).collect();
    let returntype=if ordered_outputs.is_empty(){quote!{()}}else if tuple{quote!{(#(#outtypes),*)}}else{outtypes[0].clone()};
    let returnvalue=if ordered_outputs.is_empty(){quote!{()}}else if tuple{quote!{(#(#outvalues),*)}}else{outvalues[0].clone()};
    let hframe=fresh(sm,tr,"native_hframe");let mut before_facts=vec![];
    let owner_frame=if observed_inputs.is_empty(){quote!{#completion}}
        else{quote!{Fragment #expr::op(#h,#completion)}};
    if basis.is_none(){
        for field in supplied.iter().filter(|field|
            mutable.contains(&field.name.to_string())||removed.contains_key(&field.name.to_string())
        ){
            let n=&field.name;let d=&descriptions[&n.to_string()];
            let factory=format_ident!("field_{n}");
            let own_shape=quote!{assert(#initial.#n==Fragment #expr::#factory(#d).#n);};
            let fact=match &field.stype{
                ShardableType::Option(_)=>quote!{
                    ::vstd::resource::tsm_collections::option_owned_frame(
                        #initial.#n,(#owner_frame).#n,#before.#n,#d->0);
                    assert(#before.#n==#d);
                },
                ShardableType::Variable(_)=>quote!{assert(#before.#n==#d);},
                ShardableType::Count=>quote!{assert(#before.#n>=#d);},
                ShardableType::Bool=>quote!{assert(#before.#n);},
                ShardableType::Set(_)=>quote!{
                    ::vstd::resource::tsm_collections::set_have_many_frame(
                        #initial.#n,(#owner_frame).#n,#before.#n.to_iset(),#d.to_iset());
                    assert(#d.subset_of(#before.#n));
                },
                ShardableType::Multiset(_)=>quote!{
                    ::vstd::resource::tsm_finite_multiset::finite_multiset_owned_subset(
                        #initial.#n,(#owner_frame).#n,#before.#n);
                    assert(#d.subset_of(#before.#n));
                },
                _=>quote!{},
            };
            before_facts.push(quote!{#own_shape #fact});
        }
    }
    for (input,_) in &observed_inputs{
        let field=supplied.iter().find(|f|arguments[&f.name.to_string()]==*input).unwrap();let n=&field.name;
        let d=&descriptions[&n.to_string()];let inside=fresh(sm,tr,&format!("native_inside_{n}"));
        let full=fresh(sm,tr,&format!("native_full_{n}"));
        let facts=match &field.stype{
            ShardableType::Variable(_)=>quote!{assert(#before.#n==#d);},
            ShardableType::Option(_)=>quote!{::vstd::resource::tsm_collections::option_owned_frame(#input.fragment().#n,#full.#n,#before.#n,#d->0);},
            ShardableType::PersistentOption(_)=>quote!{::vstd::resource::tsm_collections::persistent_option_owned_frame(#input.fragment().#n,#full.#n,#before.#n,#d->0);},
            ShardableType::PersistentMap(..)=>{
                if let MonoidElt::SingletonKV(original_key,_) = &have[&n.to_string()].elt{
                    let native_key=lower(original_key,&fields,&values)?;
                    quote!{::vstd::resource::tsm_collections::persistent_map_owned_frame(#input.fragment().#n,#full.#n,#before.#n.to_imap(),#native_key,#d[#native_key]);}
                }else{quote!{}}
            },_=>quote!{},
        };
        before_facts.push(quote!{
            let #full=#lift::<Protocol #types>(#input.fragment(),#h,#hframe,#before);#facts
        });
    }
    let constant_facts:Vec<_>=cn.iter().map(|n|quote!{
        ::vstd::resource::tsm_collections::persistent_option_owned_frame(
            #initial.#n,(#owner_frame).#n,Some(#before.#n),self.#n());
        assert(#before.#n==self.#n());
    }).collect();
    let geometry=if observed_inputs.is_empty(){quote!{
        assert(Fragment #expr::op(#initial,#h)==#initial);
    }}else{quote!{
        Fragment #expr::commutative(#initial,#h);
        Fragment #expr::associative(#h,#initial,#completion);
        Fragment #expr::associative(#initial,#h,#completion);
    }};
    let observed_frame=if observed_inputs.is_empty(){quote!{}}else{quote!{
        let #hframe=Fragment #expr::op(#initial,#completion);
        assert(Fragment #expr::op(#h,#hframe)==Protocol #expr::embed(#before));
    }};
    let readiness_assertion=quote!{
        reveal(Protocol::#req);
        assert forall|#completion:Fragment #types,#before:State #types|
            #before.invariant()&&Fragment #expr::op(Fragment #expr::op(#initial,#h),#completion)==Protocol #expr::embed(#before)
            implies State #expr::#enabled(#before,#(#pn),*)&&#deposit_view==State #expr::#deposited(#before,#(#pn),*)
                &&State #expr::#owners_enabled(#before,#initial,#h,#(#pn),*) by{
                    #geometry #(#constant_facts)* #observed_frame #(#before_facts)*
                };
    };
    // A separate checked lemma keeps the universal readiness proof out of
    // the actual exchange/split query. It has no tracked resource outputs.
    let separate_readiness=observed_inputs.is_empty()&&basis.is_none()&&deposits.is_empty();
    let mut readiness_declaration=TokenStream::new();
    let readiness_call=if separate_readiness{
        let ready=fresh(sm,tr,&format!("native_readiness_helper_{native_name}"));
        let mut canonical=readiness_owned_shapes[0].clone();
        for shape in readiness_owned_shapes.iter().skip(1){
            canonical=quote!{Fragment #expr::op(#canonical,#shape)};
        }
        readiness_declaration=quote!{
            proof fn #ready(tracked &self,#(#params,)*#(#readiness_descriptions)*
                #initial:Fragment #types,#h:Fragment #types,#deposit_view:IMap<#key,#stored>)
                requires #initial==#canonical,#h==Fragment #expr::empty(),
                    #deposit_view==IMap::<#key,#stored>::empty(),#(#readiness_pre,)*
                ensures Protocol #expr::#req(#initial,#h,#deposit_view,#(#pn),*)
            {
                // Readiness follows from field ownership and local preconditions.
                // The protocol invariant remains a checked, opaque premise.
                hide(State::invariant);
                #initial.op_unit();
                #readiness_assertion
            }
        };
        quote!{self.#ready(#(#pn,)*#(#readiness_values,)*#initial,#h,#deposit_view);}
    }else{quote!{
        assert(Protocol #expr::#req(#initial,#h,#deposit_view,#(#pn),*)) by {
            #readiness_assertion
        };
    }};
    // Do not hide the requirement and output relations here: any hidden
    // function makes Verus add a per-function fuel quantifier, which
    // dominated these proofs.
    let body=quote!{
        Fragment #expr::unit().op_unit();
        #(#take)*let tracked #owned=#first;#(#joins)*let #initial=#owned.fragment();
        #observe #shared_fragment
        let tracked mut #deposit:IMap<#key,#stored>=IMap::tracked_empty();#(#pack)*let #deposit_view=#deposit;
        #readiness_call
        #exchange
        let(#before,#after,#completion)=Protocol #expr::#witness(#initial,#h,#owned.fragment(),#deposit_view,#physical,#(#pn),*);
        let tracked mut #physical=#physical;#(#global_binding_defs)*#(#binding_defs)*#(#restore)*#(#extract)*#returnvalue
    };
    Ok(quote!{
        #readiness_declaration
        #(#split_helpers)*
        proof fn #raw_name(tracked &self,#(#params,)*#(#raw_inputs)*)
            ->(tracked #result:#returntype)
            requires #(#raw_pre,)*ensures #(#raw_post,)*{#body}
        pub proof fn #native_name(tracked &self,#(#params,)*#(#public_inputs)*)
            ->(tracked #result:#returntype)
            requires #(#public_pre,)*ensures #(#public_post,)*
        {#(#public_prefix)*self.#raw_name(#(#pn,)*#(#call_args),*)}
    })
}
