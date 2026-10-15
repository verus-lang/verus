//! Separating uniqueness from a real mutable owner and another borrowed owner.
use crate::ast::{Field,ShardableType,SM};
use crate::verified_field_storage_roles::Context;
use proc_macro2::TokenStream;
use quote::{format_ident,quote};
use verus_syn::Error;

pub fn agree(sm:&SM,field:&Field,cx:&Context<'_>)->Result<TokenStream,Error>{
    let name=&field.name;let types=cx.types;
    let origin=&sm.transitions[0];
    let other=crate::verified_field_storage_wide::fresh(sm,origin,&format!("agreement_other_{name}"));
    let left=crate::verified_field_storage_wide::fresh(sm,origin,&format!("agreement_left_{name}"));
    let right=crate::verified_field_storage_wide::fresh(sm,origin,&format!("agreement_right_{name}"));
    let state=crate::verified_field_storage_wide::fresh(sm,origin,&format!("agreement_state_{name}"));
    let left_frame=crate::verified_field_storage_wide::fresh(sm,origin,&format!("agreement_left_frame_{name}"));
    let right_frame=crate::verified_field_storage_wide::fresh(sm,origin,&format!("agreement_right_frame_{name}"));
    let (requires,proof)=match &field.stype{
        ShardableType::PersistentMap(..)=>(quote!{self.key()==#other.key(),},quote!{
            ::vstd::resource::tsm_collections::persistent_map_owned_frame(
                #left.fragment().#name,#left_frame.#name,#state.#name.to_imap(),self.key(),self.value());
            ::vstd::resource::tsm_collections::persistent_map_owned_frame(
                #right.fragment().#name,#right_frame.#name,#state.#name.to_imap(),#other.key(),#other.value());
        }),
        ShardableType::PersistentOption(_)=>(quote!{},quote!{
            ::vstd::resource::tsm_collections::persistent_option_owned_frame(
                #left.fragment().#name,#left_frame.#name,#state.#name,self.value());
            ::vstd::resource::tsm_collections::persistent_option_owned_frame(
                #right.fragment().#name,#right_frame.#name,#state.#name,#other.value());
        }),
        ShardableType::Variable(_)=>(quote!{},quote!{
            assert(#state.#name==self.value());
            assert(#state.#name==#other.value());
        }),
        _=>return Err(Error::new(name.span(),"readonly agreement requires Variable, PersistentOption, or PersistentMap")),
    };
    Ok(quote!{
        pub proof fn agree(tracked &self,tracked #other:&Self)
            requires self.instance_id()==#other.instance_id(),#requires
            ensures self.value()==#other.value(),
        {
            ::vstd::prelude::use_type_invariant(self);
            ::vstd::prelude::use_type_invariant(#other);
            self.metadata.agrees(&#other.metadata);
            let tracked #left=self.borrow_token();let tracked #right=#other.borrow_token();
            let (#state,#left_frame,#right_frame)=#left.compatible_with(#right);
            #proof
        }
    })
}

pub fn method(sm:&SM,field:&Field,cx:&Context<'_>)->Result<TokenStream,Error>{
    if !matches!(field.stype,ShardableType::Option(_)|ShardableType::Bool|ShardableType::Variable(_)){
        return Err(Error::new(field.name.span(),"checked uniqueness requires an exclusive role"));
    }
    let name=&field.name;let types=cx.types;let expr=cx.expr;
    let getter=format_ident!("owns_{name}");
    let helper=format_ident!("__unique_owned_{name}");
    let origin=&sm.transitions[0];
    let slot=crate::verified_field_storage_wide::fresh(sm,origin,&format!("unique_slot_{name}"));
    let other=crate::verified_field_storage_wide::fresh(sm,origin,&format!("unique_other_{name}"));
    let before=crate::verified_field_storage_wide::fresh(sm,origin,&format!("unique_before_{name}"));
    let owned=crate::verified_field_storage_wide::fresh(sm,origin,&format!("unique_owned_{name}"));
    let state=crate::verified_field_storage_wide::fresh(sm,origin,&format!("unique_state_{name}"));
    let frame=crate::verified_field_storage_wide::fresh(sm,origin,&format!("unique_frame_{name}"));
    let requirement=if matches!(field.stype,ShardableType::Bool){quote!{
        #before.#name.count==1&&#other.fragment().#name.count==1
    }}else{quote!{#before.#getter()&&#other.fragment().#getter()}};
    Ok(quote!{
        proof fn #helper(tracked #slot:&mut Tracked<Option<Token #types>>,tracked #other:&Token #types)
            requires old(#slot)@ is Some,old(#slot)@->Some_0.loc()==#other.loc(),
                {let #before=old(#slot)@->Some_0.fragment();#requirement},
            ensures false,
        {
            let tracked mut #owned=#slot.borrow_mut().tracked_take();
            let #before=#owned.fragment();
            #owned.validate_2(#other);
            let (#state,#frame)=choose|#state:State #types,#frame:Fragment #types|
                #state.invariant()&&Fragment #expr::op(
                    Fragment #expr::op(#before,#other.fragment()),#frame)==Protocol #expr::embed(#state);
            *#slot=Tracked(Some(#owned));
            assert(false);
        }
        pub proof fn unique(tracked &mut self,tracked #other:&Self)
            requires old(self).instance_id()==#other.instance_id(),
            ensures false,
        {
            ::vstd::prelude::use_type_invariant(&*self);
            ::vstd::prelude::use_type_invariant(#other);
            self.metadata.agrees(&#other.metadata);
            Self::#helper(&mut self.raw,#other.borrow_token());
        }
    })
}
