### 2023-06-07

Context: some notes about how we process traits in VIR, considerations needed for external/builtin traits, with an eye to some upcoming changes

---

Right now, the VIR ast keeps trait bounds for user-defined traits. A bunch of marker traits (like Sized) get dropped in rust_to_vir_base. We also ignore FnWithSpecification. I'm trying to decide if all that's okay as-is, and also what to do about an external trait like Allocator. It looks like VIR uses trait bounds for the following purposes:

1. recursion checking, treating trait bounds as conceptual dictionaries
2. check_functions_match in well_formed, used for decreases_by and when_used_as_spec
3. Check that there are no trait_bounds on broadcast_forall, as those would require more support to make sure they only activate when trait bounds are satisfied.

So, how does this functionality matter for all the external traits?

1. Not an issue for Sized or Allocator, these are all "nodes" that are conceptually defined before any Verus code. For FnWithSpecification, right now it only applies to closure types which can't be involved in any type cycles (enforced by Rust). Though, I have a PR that adds support for function types as well, so we'll need to start accounting for this.
2. This seems like it might be a (small) issue. If a spec function calls size_of (from Sized) or requires or ensures (from FnWithSpecification), and if an exec function redirects to that spec function via when_used_as_spec, we want to make sure that exec function also has the appropriate trait bound. However, this can easily be fixed by either remembering more traits at the VIR level or by doing the check at the Rust level. (I actually implemented this check as part of external_fn_specification, so we could just share code there.)
3. The broadcast_forall is the situation I'm most concerned about. Ideally we'd be able to write lemmas like:

```
#[broadcast_forall]
fn size_of_reference_type<V: Sized>()
  ensures size_of::<&V>() == size_of::<usize>()
```

However, this is not true for unsized types V (the reference &V is a "fat pointer" if V is unsized). So here, it's critically important the lemma only fire for types matching the trait bound. (It may also be little counterintuitive from our perspective, since we're not actually calling size_of::<V>() anywhere here.) Unfortunately, it's difficult to add a rule like "don't add a Sized trait bound to broadcast_forall lemmas" because Rust adds Sized bounds by default everywhere unless we add : ?Sized everywhere. Resolving this one way or the other is probably a blocking issue for making broadcast_forall un-trusted.

tl;dr We should probably be doing more checks relating to the trait bounds we're currently ignoring. That's not much of a problem, except for this one thorny case with broadcast_forall and Sized. However, there probably aren't any major issues with adding support for the external Allocator trait (needed to support std::Vec)
