# Supported Rust Features

Quick reference for supported Rust features. Note that this list does not include all _Verus_ features, and Verus has many spec/proof features without any standard Rust equivalent---this list only concerns Rust features. See [the guide](./modes.md) for more information about Verus' distinction between executable Rust code, specification code, and proof code.

Note that Verus is in active development. If a feature is unsupported, it might be genuinely hard, or it might just be low priority. See the [github issues](https://github.com/verus-lang/verus/issues) or [discussions](https://github.com/verus-lang/verus/discussions) for information on planned features.

**Last Updated: 2026-02-18**

<div class="table-wrapper"><table>
  <thead><tr><th colspan="2"><strong>Items</strong></th></tr></thead>
  <tbody>
  <tr>
    <td>Functions, methods, associated functions</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Associated constants</td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td>Structs</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Enums</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Const functions</td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td>Async functions</td>
    <td>Not supported</td>
  </tr>
  <tr>
    <td>Macros</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Type aliases</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Const items</td>
    <td><a href="const.html">Partially supported</a></td>
  </tr>
  <tr>
    <td>Static items</td>
    <td><a href="static.html">Partially supported</a></td>
  </tr>
  </tbody>
  <thead><tr><th colspan="2"><strong>Struct/enum definitions</strong></th></tr></thead>
  <tbody>
  <tr>
    <td>Type parameters</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Where clauses</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Lifetime parameters</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Const generics</td>
    <td>Partially Supported</td>
  </tr>
  <tr>
    <td>Custom discriminants</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>public / private fields</td>
    <td>Partially supported</td>
  </tr>
  </tbody>
  <thead><tr><th colspan="2"><strong>Expressions and Statements</strong></th></tr></thead>
  <tbody>
  <tr>
    <td>Variables, assignment, mut variables</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>If, else</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>patterns, match, if-let, match guards</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Block expressions</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Items</td>
    <td>Not supported</td>
  </tr>
  <tr>
    <td><code>loop</code>, <code>while</code></td>
    <td><a href="while.html">Supported</a></td>
  </tr>
  <tr>
    <td><code>for</code></td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td><code>?</code></td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Async blocks</td>
    <td>Not supported</td>
  </tr>
  <tr>
    <td>await</td>
    <td>Not supported</td>
  </tr>
  <tr>
    <td>Unsafe blocks</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td><code>&</code></td>
    <td>Supported</td>
  </tr>
  <tr>
    <td><code>&mut</code>, place expressions</td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td><code>==</code>, <code>!=</code></td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Type cast (<code>as</code>)</td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td>Compound assigments (<code>+=</code>, etc.)</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Array expressions</td>
    <td>Partially supported (no fill expressions with `const` arguments)</td>
  </tr>
  <tr>
    <td>Range expressions</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Index expressions</td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td>Tuple expressions</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Struct/enum constructors</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Field access</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Function and method calls</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Closures</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Labels, break, continue</td>
    <td><a href="break.html">Supported</a></td>
  </tr>
  <tr>
    <td>Return statements</td>
    <td>Supported</td>
  </tr>
  </tbody>
  <thead><tr><th colspan="2"><strong>Integer arithmetic</strong></th></tr></thead>
  <tbody>
  <tr>
    <td>Arithmetic for unsigned</td>
    <td><a href="integers.html">Supported</a></td>
  </tr>
  <tr>
    <td>Arithmetic for signed</td>
    <td><a href="integers.html">Supported</a></td>
  </tr>
  <tr>
    <td>Bitwise operations (<code>&</code>, <code>|</code>, <code>!</code>, <code>&gt;&gt;</code>, <code>&lt;&lt;</code>)</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Arch-dependent types (<code>usize</code>, <code>isize</code>)</td>
    <td>Supported</td>
  </tr>
  </tbody>
  <thead><tr><th colspan="2"><strong>Types and standard library functionality</strong></th></tr></thead>
  <tbody>
  <tr>
    <td>Integer types</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td><code>bool</code></td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Strings</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Vec</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Option / Result</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Floating point</td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td>Slices</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Arrays</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Pointers</td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td>References (<code>&</code>)</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Mutable references (<code>&mut</code>)</td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td>Never type</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Function pointer types</td>
    <td>Not supported</td>
  </tr>
  <tr>
    <td>Closure types</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Trait objects (dyn)</td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td>impl types</td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td>Cell, RefCell</td>
    <td>Not supported (see <a href="https://verus-lang.github.io/verus/verusdoc/vstd/cell/index.html">vstd alternatives</a>)</td>
  </tr>
  <tr>
    <td>Iterators</td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td><code>Vec</code>, <code>HashMap</code>, <code>HashSet</code>, <code>VecDeque</code></td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Smart pointers (<code>Box</code>, <code>Rc</code>, <code>Arc</code>)</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td><code>Pin</code></td>
    <td>Not supported</td>
  </tr>
  <tr>
    <td>Hardware intrinsics</td>
    <td>Not supported</td>
  </tr>
  <tr>
    <td>Printing, I/O</td>
    <td>Not supported</td>
  </tr>
  <tr>
    <td>Panic-unwinding</td>
    <td>Partially supported</td>
  </tr>
  </tbody>
  <thead><tr><th colspan="2"><strong>Traits</strong></th></tr></thead>
  <tbody>
  <tr>
    <td>User-defined traits</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Default implementations</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Trait bounds on trait declarations</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Traits with type arguments</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Associated types</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Generic associated types</td>
    <td>Partially supported (only lifetimes are supported)</td>
  </tr>
  <tr>
    <td>Higher-ranked trait bounds</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Marker traits (<code>Copy</code>, <code>Send</code>, <code>Sync</code>)</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>Standard traits (<code>Clone</code>, <code>Default</code>, <code>Step</code>, <code>From</code>, <code>TryFrom</code>, <code>Into</code>, <code>PartialEq</code>, <code>Eq</code>, <code>PartialOrd</code>, <code>Ord</code>, <code>Neg</code>, <code>Not</code>, <code>Add</code>, <code>Sub</code>, <code>Mul</code>, <code>Div</code>, <code>Rem</code>, <code>BitAnd</code>, <code>BitOr</code>, <code>BitXor</code>, <code>Shl</code>, <code>Shr</code>)</td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td>Standard traits (<code>Debug</code>, <code>serde::Serialize</code>)</td>
    <td>Not supported</td>
  </tr>
  <tr>
    <td>User-defined destructors (<code>Drop</code>)</td>
    <td>Not supported</td>
  </tr>
  <tr>
    <td><code>Sized</code> (<code>size_of</code>, <code>align_of</code>)</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td><code>Deref</code></td>
    <td>Supported</td>
  </tr>
  <tr>
    <td><code>DerefMut</code></td>
    <td>Not supported</td>
  </tr>
  </tbody>
  <thead><tr><th colspan="2"><strong>Multi-threading</strong></th></tr></thead>
  <tbody>
  <tr>
    <td><code>Mutex</code>, <code>RwLock</code> (from standard library)</td>
    <td>Not supported </td>
  </tr>
  <tr>
    <td>Verified lock implementations</td>
    <td>Supported </td>
  </tr>
  <tr>
    <td>Atomics</td>
    <td>Supported (<a href="https://verus-lang.github.io/verus/verusdoc/vstd/atomic_ghost/index.html">vstd equivalent</a>)</td>
  </tr>
  <tr>
    <td>spawn and join</td>
    <td><a href="https://verus-lang.github.io/verus/verusdoc/vstd/thread/index.html">Supported</a></td>
  </tr>
  <tr>
    <td>Interior mutability</td>
    <td><a href="interior_mutability.html">Supported</a></td>
  </tr>
  </tbody>
  <thead><tr><th colspan="2"><strong>Unsafe</strong></th></tr></thead>
  <tbody>
  <tr>
    <td>Raw pointers</td>
    <td><a href="https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/index.html">Partially supported</a></td>
  </tr>
  <tr>
    <td>Transmute</td>
    <td>Not supported</td>
  </tr>
  <tr>
    <td>Unions</td>
    <td><a href="reference-unions.html">Supported</a></td>
  </tr>
  <tr>
    <td><code>UnsafeCell</code></td>
    <td>Supported (<a href="https://verus-lang.github.io/verus/verusdoc/vstd/cell/struct.PCell.html">vstd equivalent</a>)</td>
  </tr>
  </tbody>
  <thead><tr><th colspan="2"><strong>Crates and code organization</strong></th></tr></thead>
  <tr>
    <td>Multi-crate projects</td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td>Verified crate + unverified crates</td>
    <td>Partially supported</td>
  </tr>
  <tr>
    <td>Modules</td>
    <td>Supported</td>
  </tr>
  <tr>
    <td>rustdoc</td>
    <td>Supported</td>
  </tr>
</table></div>
