//! Per-field actual tagged transfers for native mixed-storage adapters.
use crate::ast::{Field,ShardableType};
use proc_macro2::TokenStream;
use quote::{format_ident,quote};
use verus_syn::{Error,Type};

/// Pack an actual native value, never a ghost image of a permission.
pub fn deposit(field:&Field,key:&Type,value:&Type,actual:&verus_syn::Ident,
    combined:&verus_syn::Ident,packed:&verus_syn::Ident)->Result<TokenStream,Error>{
    if !matches!(field.stype,ShardableType::StorageOption(_)|ShardableType::StorageMap(..)){
        return Err(Error::new(field.name.span(),"wide transfer requires physical Option or finite Map"));
    }
    let pack=format_ident!("__pack_{}",field.name);
    Ok(quote!{
        let tracked #packed:IMap<#key,#value>=<#key>::#pack(#actual);
        #combined.tracked_union_prefer_right(#packed);
    })
}

/// Restrict the actual returned carrier to this original field tag, then
/// project the owned payload. Other original physical fields stay separate.
pub fn withdraw(field:&Field,key:&Type,value:&Type,returned:&verus_syn::Ident,
    witness:TokenStream,expected:&verus_syn::Ident,selected:&verus_syn::Ident,output:&verus_syn::Ident)->Result<TokenStream,Error>{
    let tag=format_ident!("__tag_{}",field.name);let untag=format_ident!("__untag_{}",field.name);
    let unpack=format_ident!("__unpack_{}",field.name);
    let finite=if matches!(field.stype,ShardableType::StorageMap(..)){
        let tag_finite=format_ident!("__tag_finite_{}",field.name);
        quote!{<#key>::#tag_finite(#witness);}
    }else{TokenStream::new()};
    let native=match &field.stype{
        ShardableType::StorageOption(_)=>witness,
        ShardableType::StorageMap(..)=>quote!{(#witness).to_imap()},
        _=>return Err(Error::new(field.name.span(),"wide transfer requires physical Option or finite Map")),
    };
    Ok(quote!{
        #finite
        let #expected=<#key>::#tag(#native);
        assert(#expected.submap_of(#returned));
        let tracked #selected:IMap<#key,#value>=#returned.tracked_remove_keys(#expected.dom());
        assert(::vstd::prelude::ext_equal(#selected,#expected));
        assert(#selected==<#key>::#tag(<#key>::#untag(#selected)));
        let tracked #output=<#key>::#unpack(#selected);
    })
}
