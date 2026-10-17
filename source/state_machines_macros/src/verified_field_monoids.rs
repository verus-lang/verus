//! Checked methods for nominal field owners, backed by their actual raw token.
//!
//! Mutable operations restore the exact sparse shape inside a raw-token helper
//! before returning to the outer nominal type's invariant boundary. These first
//! methods require the logical PCM-backed token API; storage-backed wrappers
//! need a checked take/restore slot rather than a fabricated empty owner.
//! Persistent Bool methods apply to a present field token; they clone existing
//! true evidence. False/empty bulk knowledge needs a separate nominal role.
use crate::ast::{Field, ShardableType};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use verus_syn::Error;

pub fn supported(stype: &ShardableType) -> bool {
    matches!(
        stype,
        ShardableType::Count
            | ShardableType::PersistentCount
            | ShardableType::PersistentBool
            | ShardableType::Constant(_)
    )
}

/// Emit items inside `impl FIELD`. The containing generator supplies a private
/// `raw: Token`, an exact sparse shape invariant, native `count`/`value` and
/// `instance_id` observations, and the checked `__from_token` constructor.
pub fn methods(
    field: &Field,
    fragment: &TokenStream,
    token: &TokenStream,
    protocol_expr: &TokenStream,
) -> Result<TokenStream, Error> {
    let name = &field.name;
    let factory = format_ident!("field_{}", name);
    let getter = format_ident!("value_{}", name);
    match &field.stype {
        ShardableType::Count => {
            let split = format_ident!("split_{}", name);
            let split_law = format_ident!("split_{}_law", name);
            let remove = format_ident!("remove_{}", name);
            Ok(quote! {
                proof fn __split_raw(tracked raw: &mut #token, count: nat)
                    -> (tracked out: #token)
                    requires
                        old(raw).fragment() == <#fragment>::#factory(old(raw).fragment().#getter()),
                        count <= old(raw).fragment().#getter(),
                    ensures
                        final(raw).loc() == old(raw).loc(),
                        final(raw).fragment() == <#fragment>::#factory(
                            (old(raw).fragment().#getter() - count) as nat),
                        out.loc() == old(raw).loc(),
                        out.fragment() == <#fragment>::#factory(count),
                {
                    let tracked mut owned = raw.empty();
                    ::vstd::modes::tracked_swap(raw, &mut owned);
                    let tracked (out, remainder) = #protocol_expr::#split(owned, count);
                    let tracked mut remainder = remainder;
                    ::vstd::modes::tracked_swap(raw, &mut remainder);
                    out
                }

                pub proof fn split(tracked &mut self, count: nat) -> (tracked out: Self)
                    requires count <= old(self).count(),
                    ensures
                        final(self).instance_id() == old(self).instance_id(),
                        final(self).count() == old(self).count() - count,
                        out.instance_id() == old(self).instance_id(),
                        out.count() == count,
                {
                    ::vstd::prelude::use_type_invariant(&*self);
                    let tracked out = Self::__split_raw(&mut self.raw, count);
                    Self::__from_token(out)
                }

                proof fn __join_raw(tracked raw: &mut #token, tracked other: #token)
                    requires
                        old(raw).loc() == other.loc(),
                        old(raw).fragment() == <#fragment>::#factory(old(raw).fragment().#getter()),
                        other.fragment() == <#fragment>::#factory(other.fragment().#getter()),
                    ensures
                        final(raw).loc() == old(raw).loc(),
                        final(raw).fragment() == <#fragment>::#factory(
                            old(raw).fragment().#getter() + other.fragment().#getter()),
                {
                    let first_count = raw.fragment().#getter();
                    let second_count = other.fragment().#getter();
                    let combined = <#fragment>::#factory(first_count + second_count);
                    combined.#split_law(first_count);
                    assert(combined.#remove(first_count)
                        == <#fragment>::#factory(second_count));
                    let tracked mut owned = raw.empty();
                    ::vstd::modes::tracked_swap(raw, &mut owned);
                    let tracked mut combined = owned.join(other);
                    ::vstd::modes::tracked_swap(raw, &mut combined);
                }

                pub proof fn join(tracked &mut self, tracked other: Self)
                    requires old(self).instance_id() == other.instance_id(),
                    ensures
                        final(self).instance_id() == old(self).instance_id(),
                        final(self).count() == old(self).count() + other.count(),
                {
                    ::vstd::prelude::use_type_invariant(&*self);
                    ::vstd::prelude::use_type_invariant(&other);
                    Self::__join_raw(&mut self.raw, other.raw);
                }
            })
        }
        ShardableType::PersistentCount => Ok(quote! {
            pub proof fn clone(tracked &self) -> (tracked out: Self)
                ensures
                    out.instance_id() == self.instance_id(),
                    out.count() == self.count(),
            {
                ::vstd::prelude::use_type_invariant(self);
                <#fragment>::op_unit(<#fragment>::unit());
                assert(<#fragment>::op(self.raw.fragment(), self.raw.fragment())
                    == self.raw.fragment());
                let tracked raw = self.raw.duplicate();
                Self::__from_token(raw)
            }

            pub proof fn weaken(tracked &self, count: nat) -> (tracked out: Self)
                requires count <= self.count(),
                ensures
                    out.instance_id() == self.instance_id(),
                    out.count() == count,
            {
                ::vstd::prelude::use_type_invariant(self);
                <#fragment>::op_unit(<#fragment>::unit());
                assert(<#fragment>::op(self.raw.fragment(), self.raw.fragment())
                    == self.raw.fragment());
                let weakened = <#fragment>::#factory(count);
                assert(<#fragment>::op(weakened, self.raw.fragment()) == self.raw.fragment());
                let tracked copy = self.raw.duplicate();
                let tracked (raw, remainder) = copy.split(weakened, self.raw.fragment());
                Self::__from_token(raw)
            }
        }),
        ShardableType::PersistentBool => Ok(quote! {
            pub proof fn clone(tracked &self) -> (tracked out: Self)
                ensures
                    out.instance_id() == self.instance_id(),
                    out.value() == self.value(),
            {
                ::vstd::prelude::use_type_invariant(self);
                <#fragment>::op_unit(<#fragment>::unit());
                assert(<#fragment>::op(self.raw.fragment(), self.raw.fragment())
                    == self.raw.fragment());
                let tracked raw = self.raw.duplicate();
                Self::__from_token(raw)
            }
        }),
        ShardableType::Constant(_) => Ok(quote! {
            pub proof fn clone(tracked &self) -> (tracked out: Self)
                ensures
                    out.instance_id() == self.instance_id(),
                    out.value() == self.value(),
            {
                ::vstd::prelude::use_type_invariant(self);
                <#fragment>::op_unit(<#fragment>::unit());
                assert(<#fragment>::op(self.raw.fragment(), self.raw.fragment())
                    == self.raw.fragment());
                let tracked raw = self.raw.duplicate();
                Self::__from_token(raw)
            }
        }),
        _ => Err(Error::new(
            field.name.span(),
            "nominal field monoid methods currently support count and persistent scalars",
        )),
    }
}
