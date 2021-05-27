
For lang items, consider using
https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/context/struct.TyCtxt.html#method.require_lang_item

For structural equality, consider
https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.TyS.html#method.is_structural_eq_shallow
and using a type visitor.

For field indices, consider
https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.TyCtxt.html#method.find_field_index
