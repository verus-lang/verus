# Requirements

To build the guide locally, you will need to install [mdBook](https://rust-lang.github.io/mdBook/).
The simplest approach is often to run `cargo install mdbook`.

# Building

To build the guide, run `mdbook serve`.  This will render the guide
and start a local webserver where you can view your updated guide.

# Markdown extensions

We have a couple of postprocessors to allow special stylings in the guide.

## Grammar items

The first one (`verus-grammar.py`)

First, there's the `V@` and `R@` notation, used in the reference section for grammar items.
e.g., this in src/reference-assume-specification.md:

> ```verus-grammar
> V@[assume_specification_item] ::=
>     visibility? assume_specification R@[generics]? [ R@[function_path] ] (R@[args...]) ( -> V@[exec_return_type] )?
>         R@[where_clause]?
>         V@[requires_clause]?
>         V@[ensures_clause]?
>         V@[returns_clause]?
>         V@[invariants_clause]?
>         V@[unwind_clause]?
>         ;
> ```

The V@ is used for Verus-specific concepts and R@ is used for Rust-specific concepts.
The postprocessors will automatically crosslink the pages through V@ links.

## The DIFF admoninition

mdbook has a nice feature called admonitions: https://rust-lang.github.io/mdBook/format/markdown.html?highlight=admoni#admonitions

These let you make nice-looking blocks for NOTE, TIP, etc. Our `custom-admonitions.py` adds a new DIFF admonition which is used for Verus/Rust differences (e.g., the `==` operator being different in spec code).
In principle we can add more custom admonitions.
