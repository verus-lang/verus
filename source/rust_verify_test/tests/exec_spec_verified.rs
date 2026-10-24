#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const IMPORTS: &str = code_str! {
    #[allow(unused_imports)] use vstd::prelude::*;
    #[allow(unused_imports)] use vstd::contrib::exec_spec::*;
    #[allow(unused_imports)] use vstd::multiset::*;
    #[allow(unused_imports)] use std::collections::HashSet;
    #[allow(unused_imports)] use std::collections::HashMap;
};

test_verify_one_file! {
    /// Tests basic enum compilation.
    #[test] test_exec_spec_enum IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub enum E1 {
                Blob(usize, usize),
                Seq(Seq<Seq<u32>>),
            }

            pub enum E2 {
                E1(E1),
                StructLike {
                    a: u32,
                    b: E1,
                },
                Unit,
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests basic struct compilation.
    #[test] test_exec_spec_struct IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            enum MyOption {
                Some(u32),
                None,
            }
        }

        exec_spec_verified! {
            pub struct S {
                a: u32,
                b: MyOption,
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests that compiler generates exec code with good typing.
    #[test] test_exec_spec_typing IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn id_string(s: SpecString) -> SpecString {
                s
            }

            spec fn id_u32(i: u32) -> u32 {
                i
            }

            spec fn id_seq(s: Seq<u32>) -> Seq<u32> {
                s
            }

            struct S {
                b: SpecString,
            }

            spec fn get(s: S) -> SpecString {
                let b = s.b;
                let a = id_string(b);
                a
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests compilation of literals.
    #[test] test_exec_spec_literals IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn test1(sel: bool, s: Seq<SpecString>) -> Seq<SpecString> {
                let f = if sel {
                    s
                } else {
                    seq![""@]
                };
                f
            }

            spec fn test2(sel: bool, s: Seq<SpecString>) -> Seq<SpecString> {
                let s1 = seq![""@];
                let f = if sel {
                    s
                } else {
                    s1
                };
                f
            }

            spec fn test3() -> bool {
                true
            }

            spec fn test4() -> i32 {
                123
            }

            spec fn test5() -> SpecString {
                "hello"@
            }

            spec fn test6() -> Seq<char> {
                seq!['h', 'e', 'l', 'l', 'o']
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests basic arithemetic operations.
    #[test] test_exec_spec_arith IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn square(x: u32) -> u32
                recommends x * x <= u32::MAX
            {
                (x * x) as u32
            }

            spec fn complex(x: u32) -> u32
                recommends
                    u32::MIN <= x * x <= u32::MAX,
                    u32::MIN <= x * x + x <= u32::MAX,
                    u32::MIN <= x * x + x - 2 <= u32::MAX
            {
                (x * x + x - 2) as u32
            }

            spec fn compare(x: i32, y: i32) -> bool {
                ||| x < y
                ||| x >= y
                ||| x == 1
                ||| x != 1
                ||| x != x - y
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests string indexing.
    #[test] test_exec_spec_index1 IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn test(s: SpecString, i: usize) -> char {
                if 0 <= i && i < s.len() {
                    s[i as int]
                } else {
                    ' '
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests sequence indexing
    #[test] test_exec_spec_index2 IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn test1(s: Seq<Seq<SpecString>>, i: usize, j: usize, n: usize) -> char {
                let c = if i < s.len() &&
                    j < s[i as int].len() &&
                    n < s[i as int][j as int].len() {
                    s[i as int][j as int][n as int]
                } else {
                    ' '
                };
                c
            }

            spec fn test2(s: Seq<char>, i: usize) -> char {
                if i < s.len() {
                    s[i as int]
                } else {
                    ' '
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests equality.
    #[test] test_exec_spec_equality IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn test_eq1(i: usize, j: usize) -> bool {
                i == j
            }

            spec fn test_eq2(a: SpecString, b: SpecString) -> bool {
                a == b
            }

            spec fn test_eq3(a: Seq<usize>, b: Seq<usize>) -> bool {
                a == b
            }

            spec fn test_eq4(a: Seq<SpecString>, b: Seq<SpecString>) -> bool {
                a == b
            }

            spec fn test_eq5(a: Seq<SpecString>) -> bool {
                a == seq!["hello"@, "world"@]
            }

            spec fn test_eq6(a: Seq<Seq<SpecString>>, i: usize) -> bool
                recommends 0 <= i < a.len()
            {
                a[i as int] == seq!["hello"@, "world"@]
            }

            spec fn test_eq7(a: Map<u8, u8>, b: Map<u8, u8>) -> bool
            {
                a == b
            }

            spec fn test_eq8(a: Map<u8, Seq<u8>>, b: Map<u8, Seq<u8>>) -> bool
            {
                a == b
            }

            spec fn test_eq9(a: Set<u8>, b: Set<u8>) -> bool {
                a == b
            }

            spec fn test_eq10(a: Set<Seq<u8>>, b: Set<Seq<u8>>) -> bool {
                a == b
            }

            spec fn test_eq11(a: Multiset<u8>, b: Multiset<u8>) -> bool {
                a == b
            }

            spec fn test_eq12(a: Multiset<Seq<u8>>, b: Multiset<Seq<u8>>) -> bool {
                a == b
            }

            spec fn test_eq13(a: Option<u8>, b: Option<u8>) -> bool {
                a == b
            }

            spec fn test_eq14(a: Option<Seq<u8>>, b: Option<Seq<u8>>) -> bool {
                a == b
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests match expressions.
    #[test] test_exec_spec_match IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            enum EitherString {
                Left { s1: SpecString, s2: SpecString },
                Right(SpecString),
            }

            struct GoodString {
                s: SpecString,
            }

            struct BadString(char, char);

            spec fn test_match1(s: EitherString) -> SpecString {
                match s {
                    EitherString::Left { s1, .. } => s1,
                    EitherString::Right(x) => x,
                }
            }

            spec fn test_match2(s: EitherString) -> SpecString {
                match s {
                    EitherString::Left { s1, s2: _ } => s1,
                    _ => "ello"@,
                }
            }

            spec fn test_match3(s: GoodString) -> SpecString {
                match s {
                    GoodString { s } => s,
                }
            }

            spec fn test_match4(s: BadString) -> char {
                match s {
                    BadString(c1, ..) => c1,
                }
            }

            spec fn test_tuple_struct() -> char {
                test_match4(BadString('a', 'b'))
            }

            spec fn test_match5(s: BadString) -> char {
                match s {
                    BadString(_, c2) => c2,
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests support for built-in [`Option`] type.
    #[test] test_exec_spec_option IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn test_option1(s: Option<SpecString>) -> SpecString {
                match s {
                    Some(s) => s,
                    None => "hi"@,
                }
            }

            spec fn test_option2(s: Option<SpecString>) -> bool {
                &&& test_option1(s) == match s {
                    Some(s) => s,
                    None => "ww"@,
                }
                &&& s == Some("yes"@)
            }

            spec fn test_option3(s: Option<SpecString>) -> bool
                recommends s.is_some()
            {
                s.unwrap() == "yes"@
            }

            spec fn test_option4(s: Option<SpecString>) -> SpecString {
                match s {
                    Some(_) => s.unwrap(),
                    None => "none"@,
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests support for built-in tuple types.
    #[test] test_exec_spec_tuple IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn test_tuple1(a: u32, b: u32) -> (u32, u32) {
                (a, b)
            }

            spec fn test_tuple2(a: (SpecString, u32), b: (SpecString, u32)) -> bool {
                &&& a == b
                &&& (a.0, b.1) == (b.0, a.1)
                &&& test_tuple1(a.1, b.1) == test_tuple1(b.1, a.1)
            }

            spec fn test_tuple3(a: (SpecString, u32, u8), b: (SpecString, u32, u8)) -> bool {
                &&& a == b
                &&& (a.0, a.1, a.2) == (b.0, b.1, b.2)
                &&& test_tuple2((a.0, a.1), (b.0, b.1))
            }

            spec fn test_tuple4(a: (SpecString, u32, u8, bool), b: (SpecString, u32, u8, bool)) -> bool {
                &&& a == b
                &&& (a.0, a.1, a.2, a.3) == (b.0, b.1, b.2, a.3)
                &&& test_tuple3((a.0, a.1, a.2), (b.0, b.1, b.2))
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests support for functions on Seq.
    #[test] test_exec_spec_seq IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct Inner {
                i: i64
            }

            pub struct Data {
                x: u8,
                y: Seq<u8>,
                z: (u8, u8, Inner),
            }

            spec fn add_eq(s1: Seq<u8>, s2: Seq<u8>, s3: Seq<u8>) -> bool
            {
                s1.add(s2) == s3
            }

            spec fn add_nested(s1: Seq<Seq<u8>>, s2: Seq<Seq<u8>>, s3: Seq<Seq<u8>>) -> bool
            {
                s1.add(s2) == s3
            }

            spec fn add_struct(s1: Seq<Data>, s2: Seq<Data>, s3: Seq<Data>) -> bool
            {
                s1.add(s2) == s3
            }

            spec fn contains_eq(s1: Seq<u8>, x: u8) -> bool
            {
                s1.contains(x)
            }

            spec fn contains_nested(s1: Seq<Seq<u8>>, x: Seq<u8>) -> bool
            {
                s1.contains(x)
            }

            spec fn contains_struct(s1: Seq<Data>, x: Data) -> bool
            {
                s1.contains(x)
            }

            spec fn drop_first_eq(s1: Seq<u8>, s2: Seq<u8>) -> bool
                recommends
                    s1.len() >= 1
            {
                s1.drop_first() == s2
            }

            spec fn drop_first_nested(s1: Seq<Seq<u8>>, s2: Seq<Seq<u8>>) -> bool
                recommends
                    s1.len() >= 1
            {
                s1.drop_first() == s2
            }

            spec fn drop_first_struct(s1: Seq<Data>, s2: Seq<Data>) -> bool
                recommends
                    s1.len() >= 1
            {
                s1.drop_first() == s2
            }

            spec fn drop_last_eq(s1: Seq<u8>, s2: Seq<u8>) -> bool
                recommends
                    s1.len() >= 1
            {
                s1.drop_last() == s2
            }

            spec fn drop_last_nested(s1: Seq<Seq<u8>>, s2: Seq<Seq<u8>>) -> bool
                recommends
                    s1.len() >= 1
            {
                s1.drop_last() == s2
            }

            spec fn drop_last_struct(s1: Seq<Data>, s2: Seq<Data>) -> bool
                recommends
                    s1.len() >= 1
            {
                s1.drop_last() == s2
            }

            spec fn empty_seq() -> Seq<u8>
            {
                Seq::empty()
            }

            spec fn empty_seq_length_zero() -> bool {
                empty_seq().len() == 0
            }

            spec fn first_element(s: Seq<u8>, x: u8) -> bool
                recommends
                    0 < s.len()
            {
                s.first() == x
            }

            spec fn first_nested(s: Seq<Seq<u8>>, x: Seq<u8>) -> bool
                recommends
                    0 < s.len()
            {
                s.first() == x
            }

            spec fn first_struct(s: Seq<Data>, x: Data) -> bool
                recommends
                    0 < s.len()
            {
                s.first() == x
            }

            spec fn index_eq(s: Seq<u8>, i: usize, x: u8) -> bool
                recommends
                    0 <= i < s.len()
            {
                s.index(i as int) == x
            }

            spec fn index_nested(s: Seq<Seq<u8>>, i: usize, x: Seq<u8>) -> bool
                recommends
                    0 <= i < s.len()
            {
                s.index(i as int) == x
            }

            spec fn index_struct(s: Seq<Data>, i: usize, x: Data) -> bool
                recommends
                    0 <= i < s.len()
            {
                s.index(i as int) == x
            }

            spec fn index_of_eq(s1: Seq<u8>, x: u8, i: usize) -> bool
            {
                s1.index_of(x) == i
            }

            spec fn index_of_nested(s1: Seq<Seq<u8>>, x: Seq<u8>, i: usize) -> bool
            {
                s1.index_of(x) == i
            }

            spec fn index_of_struct(s1: Seq<Data>, x: Data, i: usize) -> bool
            {
                s1.index_of(x) == i
            }

            spec fn index_of_first_eq(s1: Seq<u8>, x: u8, i: Option<usize>) -> bool
            {
                match s1.index_of_first(x) {
                    Some(n) => true,
                    None => false
                }
            }

            spec fn index_of_first_nested(s1: Seq<Seq<u8>>, x: Seq<u8>, i: Option<usize>) -> bool
            {
                s1.index_of_first(x) == match i {
                    None => None,
                    Some(n) => Some(n as int),
                }
            }

            spec fn index_of_first_struct(s1: Seq<Data>, x: Data, i: Option<usize>) -> bool
            {
                s1.index_of_first(x) == match i {
                    None => None,
                    Some(n) => Some(n as int),
                }
            }

            spec fn index_of_last_eq(s1: Seq<u8>, x: u8, i: Option<usize>) -> bool
            {
                s1.index_of_last(x) == match i {
                    None => None,
                    Some(n) => Some(n as int),
                }
            }

            spec fn index_of_last_nested(s1: Seq<Seq<u8>>, x: Seq<u8>, i: Option<usize>) -> bool
            {
                s1.index_of_last(x) == match i {
                    None => None,
                    Some(n) => Some(n as int),
                }
            }

            spec fn index_of_last_struct(s1: Seq<Data>, x: Data, i: Option<usize>) -> bool
            {
                s1.index_of_last(x) == match i {
                    None => None,
                    Some(n) => Some(n as int),
                }
            }

            spec fn is_prefix_of_eq(s1: Seq<u8>, s2: Seq<u8>) -> bool
            {
                s1.is_prefix_of(s2)
            }

            spec fn is_prefix_of_nested(s1: Seq<Seq<u8>>, s2: Seq<Seq<u8>>) -> bool
            {
                s1.is_prefix_of(s2)
            }

            spec fn is_prefix_of_struct(s1: Seq<Data>, s2: Seq<Data>) -> bool
            {
                s1.is_prefix_of(s2)
            }

            spec fn is_suffix_of_eq(s1: Seq<u8>, s2: Seq<u8>) -> bool
            {
                s1.is_suffix_of(s2)
            }

            spec fn is_suffix_of_nested(s1: Seq<Seq<u8>>, s2: Seq<Seq<u8>>) -> bool
            {
                s1.is_suffix_of(s2)
            }

            spec fn is_suffix_of_struct(s1: Seq<Data>, s2: Seq<Data>) -> bool
            {
                s1.is_suffix_of(s2)
            }

            spec fn last_element(s: Seq<u8>, x: u8) -> bool
                recommends
                    0 < s.len()
            {
                s.last() == x
            }

            spec fn last_nested(s: Seq<Seq<u8>>, x: Seq<u8>) -> bool
                recommends
                    0 < s.len()
            {
                s.last() == x
            }

            spec fn last_struct(s: Seq<Data>, x: Data) -> bool
                recommends
                    0 < s.len()
            {
                s.last() == x
            }

            spec fn push_element(s1: Seq<u8>, x: u8, s2: Seq<u8>) -> bool
            {
                s1.push(x) == s2
            }

            spec fn push_nested(s1: Seq<Seq<u8>>, x: Seq<u8>, s2: Seq<Seq<u8>>) -> bool
            {
                s1.push(x) == s2
            }

            spec fn push_struct(s1: Seq<Data>, x: Data, s2: Seq<Data>) -> bool
            {
                s1.push(x) == s2
            }

            spec fn skip_eq(s1: Seq<u8>, n: usize, s2: Seq<u8>) -> bool
                recommends
                    0 <= n <= s1.len()
            {
                s1.skip(n as int) == s2
            }

            spec fn skip_nested(s1: Seq<Seq<u8>>, n: usize, s2: Seq<Seq<u8>>) -> bool
                recommends
                    0 <= n <= s1.len()
            {
                s1.skip(n as int) == s2
            }

            spec fn skip_struct(s1: Seq<Data>, n: usize, s2: Seq<Data>) -> bool
                recommends
                    0 <= n <= s1.len()
            {
                s1.skip(n as int) == s2
            }

            spec fn subrange_eq(s1: Seq<u8>, s: usize, e: usize, s2: Seq<u8>) -> bool
                recommends
                    0 <= s <= e <= s1.len()
            {
                s1.subrange(s as int, e as int) == s2
            }

            spec fn subrange_nested(s1: Seq<Seq<u8>>, s: usize, e: usize, s2: Seq<Seq<u8>>) -> bool
                recommends
                    0 <= s <= e <= s1.len()
            {
                s1.subrange(s as int, e as int) == s2
            }

            spec fn subrange_struct(s1: Seq<Data>, s: usize, e: usize, s2: Seq<Data>) -> bool
                recommends
                    0 <= s <= e <= s1.len()
            {
                s1.subrange(s as int, e as int) == s2
            }

            spec fn take_eq(s1: Seq<u8>, n: usize, s2: Seq<u8>) -> bool
                recommends
                    0 <= n <= s1.len()
            {
                s1.take(n as int) == s2
            }

            spec fn take_nested(s1: Seq<Seq<u8>>, n: usize, s2: Seq<Seq<u8>>) -> bool
                recommends
                    0 <= n <= s1.len()
            {
                s1.take(n as int) == s2
            }

            spec fn take_struct(s1: Seq<Data>, n: usize, s2: Seq<Data>) -> bool
                recommends
                    0 <= n <= s1.len()
            {
                s1.take(n as int) == s2
            }

            spec fn to_multiset_eq(s: Seq<u8>, m: Multiset<u8>) -> bool
            {
                s.to_multiset() == m
            }

            spec fn seq_to_multiset_count(s: Seq<u8>, m: Multiset<u8>, e: u8) -> bool
            {
                s.to_multiset().count(e) == m.count(e)
            }

            spec fn update_eq(s1: Seq<u8>, i: usize, x: u8, s2: Seq<u8>) -> bool
                recommends
                    0 <= i < s1.len()
            {
                s1.update(i as int, x) == s2
            }

            spec fn update_nested(s1: Seq<Seq<u8>>, i: usize, x: Seq<u8>, s2: Seq<Seq<u8>>) -> bool
                recommends
                    0 <= i < s1.len()
            {
                s1.update(i as int, x) == s2
            }

            spec fn update_struct(s1: Seq<Data>, i: usize, x: Data, s2: Seq<Data>) -> bool
                recommends
                    0 <= i < s1.len()
            {
                s1.update(i as int, x) == s2
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_spec_seq_update IMPORTS.to_string() + verus_code_str! {
        fn test_update() {
            let v = vec![1u8];
            let updated = v.as_slice().exec_update(0, 2);
            assert(updated.deep_view() =~= seq![2u8]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_spec_seq_update_requires IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn update_at(s: Seq<u8>, i: usize, x: u8) -> Seq<u8> {
                s.update(i as int, x) // FAILS
            }
        }

        fn test_update() {
            let v = vec![1u8];
            let _ = v.as_slice().exec_update(1, 2); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    /// Tests support for functions on Set.
    #[test] test_exec_spec_set IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct Inner {
                i: i64
            }

            pub struct Data {
                x: u8,
                y: Seq<u8>,
                z: (u8, u8, Inner),
            }

            spec fn contains_eq(m1: Set<u8>, k: u8) -> bool
            {
                m1.contains(k)
            }

            spec fn contains_nested(m1: Set<Seq<u8>>, k: Seq<u8>) -> bool
            {
                m1.contains(k)
            }

            spec fn contains_struct(m1: Set<Data>, k: Data) -> bool
            {
                m1.contains(k)
            }

            spec fn difference_eq(m1: Set<u8>, m2: Set<u8>, m3: Set<u8>) -> bool
            {
                m1.difference(m2) == m3
            }

            spec fn difference_nested(m1: Set<Seq<u8>>, m2: Set<Seq<u8>>, m3: Set<Seq<u8>>) -> bool
            {
                m1.difference(m2) == m3
            }

            spec fn difference_struct(m1: Set<Data>, m2: Set<Data>, m3: Set<Data>) -> bool
            {
                m1.difference(m2) == m3
            }

            spec fn empty_set() -> Set<u8>
            {
                Set::empty()
            }

            spec fn empty_set_length_zero() -> bool {
                empty_set().len() == 0
            }

            spec fn insert_eq(m1: Set<u8>, k: u8, m2: Set<u8>) -> bool
            {
                m1.insert(k) == m2
            }

            spec fn insert_nested(m1: Set<Seq<u8>>, k: Seq<u8>, m2: Set<Seq<u8>>) -> bool
            {
                m1.insert(k) == m2
            }

            spec fn insert_struct(m1: Set<Data>, k: Data, m3: Set<Data>) -> bool
            {
                m1.insert(k) == m3
            }

            spec fn intersect_eq(m1: Set<u8>, m2: Set<u8>, m3: Set<u8>) -> bool
            {
                m1.intersect(m2) == m3
            }

            spec fn intersect_nested(m1: Set<Seq<u8>>, m2: Set<Seq<u8>>, m3: Set<Seq<u8>>) -> bool
            {
                m1.intersect(m2) == m3
            }

            spec fn intersect_struct(m1: Set<Data>, m2: Set<Data>, m3: Set<Data>) -> bool
            {
                m1.intersect(m2) == m3
            }

            spec fn len_eq(m1: Set<u8>, n: usize) -> bool
            {
                m1.len() == n as int
            }

            spec fn len_struct(m1: Set<Data>, n: usize) -> bool
            {
                m1.len() == n as int
            }

            spec fn remove_eq(m1: Set<u8>, k: u8, m2: Set<u8>) -> bool
            {
                m1.remove(k) == m2
            }

            spec fn remove_nested(m1: Set<Seq<u8>>, k: Seq<u8>, m2: Set<Seq<u8>>) -> bool
            {
                m1.remove(k) == m2
            }

            spec fn remove_struct(m1: Set<Data>, k: Data, m2: Set<Data>) -> bool
            {
                m1.remove(k) == m2
            }

            spec fn union_eq(m1: Set<u8>, m2: Set<u8>, m3: Set<u8>) -> bool
            {
                m1.union(m2) == m3
            }

            spec fn union_nested(m1: Set<Seq<u8>>, m2: Set<Seq<u8>>, m3: Set<Seq<u8>>) -> bool
            {
                m1.union(m2) == m3
            }

            spec fn union_struct(m1: Set<Data>, m2: Set<Data>, m3: Set<Data>) -> bool
            {
                m1.union(m2) == m3
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests support for functions on Map.
    #[test] test_exec_spec_map IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct Inner {
                i: i64
            }

            pub struct Data {
                x: u8,
                y: Seq<u8>,
                z: (u8, u8, Inner),
            }

            spec fn dom_eq(m1: Map<u8, u8>, s: Set<u8>) -> bool
            {
                m1.dom() == s
            }

            spec fn dom_struct(m1: Map<Data, u8>, s: Set<Data>) -> bool
            {
                m1.dom() == s
            }

            spec fn empty_map() -> Map<u8, u8>
            {
                Map::empty()
            }

            spec fn empty_map_length_zero() -> bool {
                empty_map().len() == 0
            }

            spec fn get_eq(m1: Map<u8, u8>, k: u8, v: u8) -> bool
            {
                m1.get(k) == Some(v)
            }

            spec fn get_nested(m1: Map<Seq<u8>, u8>, k: Seq<u8>, v: u8) -> bool
            {
                m1.get(k) == Some(v)
            }

            spec fn get_struct(m1: Map<Data, u8>, k: Data, v: u8) -> bool
            {
                m1.get(k) == Some(v)
            }

            spec fn index_eq(m1: Map<u8, u8>, k: u8, v: u8) -> bool
                recommends m1.dom().contains(k)
            {
                m1[k] == v
            }

            spec fn index_method_eq(m1: Map<u8, u8>, k: u8, v: u8) -> bool
                recommends m1.dom().contains(k)
            {
                m1.index(k) == v
            }

            spec fn insert_eq(m1: Map<u8, u8>, k: u8, v: u8, m2: Map<u8, u8>) -> bool
            {
                m1.insert(k, v) == m2
            }

            spec fn insert_nested(m1: Map<Seq<u8>, u8>, k: Seq<u8>, v: u8, m2: Map<Seq<u8>, u8>) -> bool
            {
                m1.insert(k, v) == m2
            }

            spec fn insert_nested_key(m1: Map<Seq<u8>, Seq<u8>>, k: Seq<u8>, v: Seq<u8>, m2: Map<Seq<u8>, Seq<u8>>) -> bool
            {
                m1.insert(k, v) == m2
            }

            spec fn insert_struct(m1: Map<Data, u8>, k: Data, v: u8, m2: Map<Data, u8>) -> bool
            {
                m1.insert(k, v) == m2
            }

            spec fn len_eq(m1: Map<u8, u8>, n: usize) -> bool
            {
                m1.len() == n as int
            }

            spec fn len_struct(m1: Map<u8, Data>, n: usize) -> bool
            {
                m1.len() == n as int
            }

            spec fn remove_eq(m1: Map<u8, u8>, k: u8, m2: Map<u8, u8>) -> bool
            {
                m1.remove(k) == m2
            }

            spec fn remove_nested(m1: Map<Seq<u8>, u8>, k: Seq<u8>, m2: Map<Seq<u8>, u8>) -> bool
            {
                m1.remove(k) == m2
            }

            spec fn remove_struct(m1: Map<Data, u8>, k: Data, m2: Map<Data, u8>) -> bool
            {
                m1.remove(k) == m2
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests support for functions on Multiset.
    #[test] test_exec_spec_multiset IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct Inner {
                i: i64
            }

            pub struct Data {
                x: u8,
                y: Seq<u8>,
                z: (u8, u8, Inner),
            }

            spec fn add_eq(m1: Multiset<u8>, m2: Multiset<u8>, m3: Multiset<u8>) -> bool
            {
                m1.add(m2) == m3
            }

            spec fn add_nested(m1: Multiset<Seq<u8>>, m2: Multiset<Seq<u8>>, m3: Multiset<Seq<u8>>) -> bool {
                m1.add(m2) == m3
            }

            spec fn add_struct(m1: Multiset<Data>, m2: Multiset<Data>, m3: Multiset<Data>) -> bool {
                m1.add(m2) == m3
            }

            spec fn count_eq(s: Multiset<u8>, value: u8, c: usize) -> bool
            {
                s.count(value) == c as nat
            }

            spec fn count_nested(s: Multiset<Seq<Seq<u8>>>, value: Seq<Seq<u8>>, c: usize) -> bool
            {
                s.count(value) == c as nat
            }

            spec fn count_struct(s: Multiset<Data>, value: Data, c: usize) -> bool
            {
                s.count(value) == c as nat
            }

            spec fn empty_multiset() -> Multiset<u8>
            {
                Multiset::empty()
            }

            spec fn empty_multiset_length_zero() -> bool {
                empty_multiset().len() == 0
            }

            spec fn test(s: Multiset<u8>, i: usize) -> bool
            {
                s.len() == i as nat
            }

            spec fn test_struct(s: Multiset<Data>, i: usize) -> bool
            {
                s.len() == i as nat
            }

            spec fn singleton_eq(v: u8, m: Multiset<u8>) -> bool
            {
                Multiset::singleton(v) == m
            }

            spec fn singleton_nested(v: Seq<u8>, m: Multiset<Seq<u8>>) -> bool {
                Multiset::singleton(v) == m
            }

            spec fn singleton_struct(v: Data, m: Multiset<Data>) -> bool {
                Multiset::singleton(v) == m
            }

            spec fn sub_eq(m1: Multiset<u8>, m2: Multiset<u8>, m3: Multiset<u8>) -> bool
            {
                m1.sub(m2) == m3
            }

            spec fn sub_nested(m1: Multiset<Seq<u8>>, m2: Multiset<Seq<u8>>, m3: Multiset<Seq<u8>>) -> bool {
                m1.sub(m2) == m3
            }

            spec fn sub_struct(m1: Multiset<Data>, m2: Multiset<Data>, m3: Multiset<Data>) -> bool {
                m1.sub(m2) == m3
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests struct/enum constructors.
    #[test] test_exec_spec_constructor IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            struct A {
                a: u32,
                b: u32,
            }

            enum B {
                C {
                    a: A,
                }
            }

            spec fn test_struct(a: u32, b: u32) -> A {
                A { a, b }
            }

            spec fn test_struct2(a: A) -> (B, (B, B)) {
                let x = B::C { a };
                let y = B::C {
                    a: test_struct(a.a, a.b),
                };
                (B::C {
                    a: A {
                        a: a.a,
                        b: a.b,
                    },
                }, (x, y))
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests `matches`.
    #[test] test_exec_spec_matches IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            enum D {
                E, F
            }

            enum C {
                A, B(D)
            }

            spec fn test_matches1(x: C) -> bool {
                ||| x matches C::B(y) && y matches D::E
                ||| x matches C::B(D::F) ==> x matches C::A
                ||| {
                    &&& x matches C::B(z)
                    &&& z matches D::F
                }
            }

            spec fn test_matches2(x: Option<Option<C>>) -> bool {
                ||| x matches Some(_)
                ||| x matches Some(Some(x)) ==> x matches C::A
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests support for recursions and `decreases` clauses.
    #[test] test_exec_spec_recursion IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn test_recursion1(n: usize) -> usize
                decreases n
            {
                if n == 0 {
                    0
                } else {
                    test_recursion1((n - 1) as usize)
                }
            }

            spec fn test_recursion2(n: i32) -> i32
                decreases n when n >= 0
            {
                if n == 0 {
                    1
                } else {
                    test_recursion2((n - 1) as i32)
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests support for recursion with sequence.
    #[test] test_exec_spec_recursion_seq IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn test_all_positive(a: Seq<i32>, i: usize) -> bool
                recommends 0 <= i < a.len()
                decreases a.len() - i when i < usize::MAX
            {
                &&& a[i as int] > 0
                &&& i + 1 < a.len() ==> test_all_positive(a, (i + 1) as usize)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests support for some built-in constants.
    #[test] test_exec_spec_constant IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn test(i: usize) -> bool {
                usize::MAX - i != 0
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests interoperability and generated post/pre-conditions
    #[test] test_exec_spec_interop1 IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn test_all_positive(a: Seq<i32>, i: usize) -> bool
                recommends 0 <= i < a.len()
                decreases a.len() - i when i < usize::MAX
            {
                &&& a[i as int] > 0
                &&& i + 1 < a.len() ==> test_all_positive(a, (i + 1) as usize)
            }
        }

        fn sanity_check() {
            reveal_with_fuel(test_all_positive, 3);
            assert(test_all_positive(seq![1, 2, 3], 0));
            let res = exec_test_all_positive(&[1, 2, 3], 0);
            assert(res);
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests interoperability and generated post/pre-conditions.
    #[test] test_exec_spec_interop2 IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            struct A {
                a: u32,
                b: u32,
            }

            spec fn pred(a: A) -> bool {
                a.a > a.b
            }
        }

        fn sanity_check() {
            let a = ExecA { a: 3, b: 2 };

            if exec_pred(&a) {
                assert(a.a > a.b);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests interoperability and generated post/pre-conditions.
    #[test] test_exec_spec_interop3 IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            struct MyPair(Seq<u32>, Seq<u32>);

            spec fn pred_helper(a: Seq<u32>, b: Seq<u32>, i: usize) -> bool
                recommends 0 <= i < a.len() == b.len()
                decreases a.len() - i when i < usize::MAX
            {
                &&& a[i as int] > b[i as int]
                &&& i + 1 < a.len() ==> pred_helper(a, b, (i + 1) as usize)
            }

            spec fn pred(p: MyPair) -> bool
                recommends p.0.len() == p.1.len()
            {
                if p.0.len() == 0 {
                    true
                } else {
                    pred_helper(p.0, p.1, 0)
                }
            }
        }

        fn test() {
            let a = ExecMyPair(vec![1, 2, 3], vec![0, 1, 2]);

            reveal_with_fuel(pred_helper, 3);

            if exec_pred(&a) {
                assert(a.0@[0] > a.1@[0]);
                assert(a.0@[1] > a.1@[1]);
                assert(a.0@[2] > a.1@[2]);
            } else {
                assert(a.0@[0] <= a.1@[0] || a.0@[1] <= a.1@[1] || a.0@[2] <= a.1@[2]);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests that error spans are accurate.
    #[test] test_exec_spec_error_span IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            struct MyPair(Seq<u32>, Seq<u32>);

            spec fn pred(p: MyPair) -> bool
                recommends p.0.len() != 0
            {
                p.0[0] + 10 > 100 // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    /// Tests that linear variables are compiled correctly.
    #[test] test_exec_spec_linear IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            struct B;

            struct A {
                x: B,
                y: B,
            }

            spec fn test1(a: A) -> bool {
                let b = a;
                let c = b;
                let d = b;
                true
            }

            spec fn test2(a: A) -> B {
                let b = a.x;
                let e = {
                    let c = b;
                    let d = b;
                    d
                };
                e
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests complex structs/enums from the X.509 project.
    #[test] test_exec_spec_certificate IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct Attribute {
                pub oid: SpecString,
                pub value: SpecString,
            }

            pub struct DistinguishedName(pub Seq<Seq<Attribute>>);

            pub enum GeneralName {
                DNSName(SpecString),
                DirectoryName(DistinguishedName),
                IPAddr(Seq<u8>),
                OtherName,
                Unsupported,
            }

            pub enum SubjectKey {
                RSA {
                    mod_length: usize,
                },
                DSA {
                    p_len: usize,
                    q_len: usize,
                    g_len: usize,
                },
                Other,
            }

            pub struct AuthorityKeyIdentifier {
                pub critical: Option<bool>,
                pub key_id: Option<SpecString>,
                pub issuer: Option<SpecString>,
                pub serial: Option<SpecString>,
            }

            pub struct SubjectKeyIdentifier {
                pub critical: Option<bool>,
                pub key_id: SpecString,
            }

            pub enum ExtendedKeyUsageType {
                ServerAuth,
                ClientAuth,
                CodeSigning,
                EmailProtection,
                TimeStamping,
                OCSPSigning,
                Any,
                Other(SpecString),
            }

            pub struct ExtendedKeyUsage {
                pub critical: Option<bool>,
                pub usages: Seq<ExtendedKeyUsageType>,
            }

            pub struct BasicConstraints {
                pub critical: Option<bool>,
                pub is_ca: bool,
                pub path_len: Option<i64>,
            }

            pub struct KeyUsage {
                pub critical: Option<bool>,
                pub digital_signature: bool,
                pub non_repudiation: bool,
                pub key_encipherment: bool,
                pub data_encipherment: bool,
                pub key_agreement: bool,
                pub key_cert_sign: bool,
                pub crl_sign: bool,
                pub encipher_only: bool,
                pub decipher_only: bool,
            }

            pub struct SubjectAltName {
                pub critical: Option<bool>,
                pub names: Seq<GeneralName>,
            }

            pub struct NameConstraints {
                pub critical: Option<bool>,
                pub permitted: Seq<GeneralName>,
                pub excluded: Seq<GeneralName>,
            }

            pub struct CertificatePolicies {
                pub critical: Option<bool>,
                pub policies: Seq<SpecString>,
            }

            pub struct AuthorityInfoAccess {
                pub critical: Option<bool>,
                // Other info is not encoded
            }

            pub struct SignatureAlgorithm {
                pub id: SpecString,
                pub bytes: SpecString,
            }

            pub struct Extension {
                pub oid: SpecString,
                pub critical: Option<bool>,
            }

            pub struct Certificate {
                pub fingerprint: SpecString,
                pub version: u32,
                pub serial: SpecString,
                pub sig_alg_outer: SignatureAlgorithm,
                pub sig_alg_inner: SignatureAlgorithm,
                pub not_after: u64,
                pub not_before: u64,

                pub issuer: DistinguishedName,
                pub subject: DistinguishedName,
                pub subject_key: SubjectKey,

                pub issuer_uid: Option<SpecString>,
                pub subject_uid: Option<SpecString>,

                pub ext_authority_key_id: Option<AuthorityKeyIdentifier>,
                pub ext_subject_key_id: Option<SubjectKeyIdentifier>,
                pub ext_extended_key_usage: Option<ExtendedKeyUsage>,
                pub ext_basic_constraints: Option<BasicConstraints>,
                pub ext_key_usage: Option<KeyUsage>,
                pub ext_subject_alt_name: Option<SubjectAltName>,
                pub ext_name_constraints: Option<NameConstraints>,
                pub ext_certificate_policies: Option<CertificatePolicies>,
                pub ext_authority_info_access: Option<AuthorityInfoAccess>,

                // All extensions without parameters
                pub all_exts: Option<Seq<Extension>>,
            }

            pub enum Purpose {
                ServerAuth,
            }

            pub struct Task {
                pub hostname: Option<SpecString>,
                pub purpose: Purpose,
                pub now: u64,
            }

            pub enum PolicyError {
                UnsupportedTask,
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests basic `forall` expressions.
    #[test] test_exec_spec_basic_forall IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn zero_vec(a: Seq<u32>) -> bool {
                forall |i: usize| 0 <= i < a.len() ==> a[i as int] != 0
            }
        }

        fn sanity_check() {
            let v = vec![1, 2, 3];
            if exec_zero_vec(&v) {
                assert(v.deep_view()[0] != 0);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests basic `exists` expressions.
    #[test] test_exec_spec_basic_exists IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn non_zero_vec(a: Seq<u32>) -> bool {
                exists |i: usize| 0 <= i < a.len() && a[i as int] != 0
            }
        }

        fn sanity_check() {
            let v = vec![1, 2, 3];
            if exec_non_zero_vec(&v) {
                assert(non_zero_vec(v.deep_view()));
                assert(exists |i: usize| 0 <= i < v.deep_view().len() && v.deep_view()[i as int] != 0);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests different bound expressions for quantifiers
    #[test] test_exec_spec_quant_bounds IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn eq_0(i: usize) -> bool {
                i == 0
            }

            spec fn eq_10(i: usize) -> bool {
                i == 10
            }

            spec fn neq_0(i: usize) -> bool {
                i != 0
            }

            spec fn neq_10(i: usize) -> bool {
                i != 10
            }

            spec fn le_le_0_10(i: usize) -> bool {
                0 <= i && i <= 10
            }

            spec fn lt_lt_forall() -> bool
            {
                forall |i: usize| 0 < i < 10 ==> neq_0(i) && neq_10(i)
            }

            spec fn le_lt_forall() -> bool {
                forall |i: usize| 0 <= i < 10 ==> neq_10(i)
            }

            spec fn lt_le_forall() -> bool {
                forall |i: usize| 0 < i <= 10 ==> neq_0(i)
            }

            spec fn le_le_forall() -> bool {
                forall |i: usize| 0 <= i <= 10 ==> le_le_0_10(i)
            }

            spec fn lt_lt_exists() -> bool
            {
                !(exists |i: usize| 0 < i < 10 && (eq_0(i) || eq_10(i)))
            }

            spec fn le_lt_exists() -> bool {
                exists |i: usize| 0 <= i < 10 && eq_0(i)
            }

            spec fn lt_le_exists() -> bool {
                exists |i: usize| 0 < i <= 10 && eq_10(i)
            }

            spec fn le_le_exists() -> bool {
                exists |i: usize| 0 <= i <= 10 && eq_10(i)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests nested `forall`s.
    #[test] test_exec_spec_nested_foralls IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn distinct(a: Seq<u32>) -> bool {
                forall |i: usize| #![trigger a[i as int]] 0 <= i < a.len() ==>
                forall |j: usize| #![trigger a[j as int]] 0 <= j < i ==>
                    a[i as int] != a[j as int]
            }
        }

        fn sanity_check(v: Vec<u32>) {
            if exec_distinct(&v) {
                assert(v.deep_view().len() >= 2 ==> v.deep_view()[0] != v.deep_view()[1]);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests nested `exists`s.
    #[test] test_exec_spec_nested_exists IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn has_duplicate(a: Seq<u32>) -> bool {
                exists |i: usize| #![trigger a[i as int]] 0 <= i < a.len() &&
                exists |j: usize| #![trigger a[j as int]] 0 <= j < i &&
                    a[i as int] == a[j as int]
            }
        }

        fn sanity_check(v: Vec<u32>) {
            if exec_has_duplicate(&v) {
                assert(v.deep_view().len() == 2 ==> v.deep_view()[0] == v.deep_view()[1]);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests alternating quantifiers.
    /// Currently ignored because it contains a trigger loop and is thus flaky.
    #[ignore] #[test] test_exec_spec_alt_quants IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn has_unique_maximum(a: Seq<u32>) -> bool {
                exists |i: usize| #![trigger a[i as int]] 0 <= i < a.len() &&
                    forall |j: usize| #![trigger a[j as int]] 0 <= j < a.len() ==>
                        i == j || a[i as int] > a[j as int]
            }
        }

        fn sanity_check(v: Vec<u32>) {
            if exec_has_unique_maximum(&v) {
                assert(v.deep_view().len() == 2 ==>
                    v.deep_view()[0] > v.deep_view()[1] ||
                    v.deep_view()[0] < v.deep_view()[1]);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Inherent impl on a struct: `&self` method using fields, with `recommends`
    /// referencing `self` as well.
    #[test] test_exec_spec_impl_struct IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct Pair {
                pub x: u32,
                pub y: u32,
            }

            impl Pair {
                pub open spec fn sum(&self) -> u32
                    recommends self.x + self.y <= u32::MAX
                {
                    (self.x + self.y) as u32
                }

                pub open spec fn max(&self) -> u32 {
                    if self.x >= self.y { self.x } else { self.y }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Inherent impl on an enum: `&self` method using `match self`.
    #[test] test_exec_spec_impl_enum IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub enum E {
                A(u32),
                B { v: u32 },
                C,
            }

            impl E {
                pub open spec fn tag(&self) -> u32 {
                    match self {
                        E::A(_) => 0,
                        E::B { .. } => 1,
                        E::C => 2,
                    }
                }

                pub open spec fn is_c(&self) -> bool {
                    match self {
                        E::C => true,
                        _ => false,
                    }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Recursive method with `decreases` referencing `self`.
    #[test] test_exec_spec_impl_self_recursion IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct Counter {
                pub n: u32,
            }

            impl Counter {
                pub open spec fn count_down(&self) -> u32
                    decreases self.n
                {
                    if self.n == 0 {
                        0
                    } else {
                        let next = Counter { n: (self.n - 1) as u32 };
                        next.count_down()
                    }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Recursive method on an enum (linked list shape).
    #[test] test_exec_spec_impl_enum_recursion IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub enum List {
                Cons(u32, Seq<u32>),
                Nil,
            }

            impl List {
                pub open spec fn is_nil(&self) -> bool {
                    match self {
                        List::Cons(..) => false,
                        List::Nil => true,
                    }
                }
            }

            // Free-standing recursion that calls a method on each step.
            spec fn count_nils(l: List, n: usize) -> u32
                decreases n
            {
                if n == 0 {
                    0
                } else if l.is_nil() {
                    1
                } else {
                    0
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// `decreases ... when ...` clause referencing `self`, using a `decreases self` pattern.
    #[test] test_exec_spec_impl_decreases_when IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct Counter {
                pub n: i32,
            }

            impl Counter {
                pub open spec fn down(&self) -> i32
                    decreases self.n when self.n >= 0
                {
                    if self.n == 0 {
                        1
                    } else {
                        let next = Counter { n: (self.n - 1) as i32 };
                        next.down()
                    }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Method body uses `match self` and post-condition `=~~=` against the
    /// spec's match result, exercising the deep-view ext-eq path.
    #[test] test_exec_spec_impl_matching_spec IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub enum Shape {
                Square,
                Rect,
            }

            impl Shape {
                pub open spec fn is_square(&self) -> bool {
                    match self {
                        Shape::Square => true,
                        Shape::Rect => false,
                    }
                }

                pub open spec fn is_rect(&self) -> bool {
                    match self {
                        Shape::Square => false,
                        Shape::Rect => true,
                    }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Free-standing function calls a user-defined method (exercises the
    /// `Expr::MethodCall` fallthrough into `exec_<name>`).
    #[test] test_exec_spec_impl_method_call_site IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct Pair {
                pub x: u32,
                pub y: u32,
            }

            impl Pair {
                pub open spec fn sum(&self) -> u32
                    recommends self.x <= 1000, self.y <= 1000
                {
                    (self.x + self.y) as u32
                }
            }

            spec fn add_pairs(p: Pair, q: Pair) -> u32
                recommends
                    p.x <= 1000, p.y <= 1000,
                    q.x <= 1000, q.y <= 1000,
            {
                (p.sum() + q.sum()) as u32
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// `&self` is supported. Using `self` by value or `&mut self` is rejected.
    #[test] test_exec_spec_impl_ref_self_supported IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct W { pub v: u32 }

            impl W {
                pub open spec fn get(&self) -> u32 {
                    self.v
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// `self` by value is rejected with a clear error.
    #[test] test_exec_spec_impl_value_self_rejected IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct W { pub v: u32 }

            impl W {
                pub open spec fn get(self) -> u32 {
                    self.v
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "only `&self` is supported")
}

test_verify_one_file! {
    /// `&mut self` is rejected (spec methods are pure).
    #[test] test_exec_spec_impl_mut_self_rejected IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct W { pub v: u32 }

            impl W {
                pub open spec fn get(&mut self) -> u32 {
                    self.v
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`&mut self` is not supported")
}

test_verify_one_file! {
    /// Trait impls are not supported in `exec_spec_verified!`.
    #[test] test_exec_spec_impl_trait_rejected IMPORTS.to_string() + verus_code_str! {
        trait MyTrait {
            spec fn label() -> u32;
        }

        exec_spec_verified! {
            pub struct S { pub v: u32 }

            impl MyTrait for S {
                open spec fn label() -> u32 { 0 }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "trait impls not supported in exec_spec")
}

test_verify_one_file! {
    /// Generic impls are not supported.
    #[test] test_exec_spec_impl_generics_rejected IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct W { pub v: u32 }

            impl<T> W {
                pub open spec fn get(&self) -> u32 { self.v }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "generics not supported")
}

test_verify_one_file! {
    /// Mix of `pub closed` and `pub open` spec functions in the same macro
    /// invocation.
    #[test] test_exec_spec_closed_and_open_fns IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub closed spec fn squared(x: u32) -> u32
                recommends x * x <= u32::MAX
            {
                (x * x) as u32
            }

            pub open spec fn doubled(x: u32) -> u32
                recommends x + x <= u32::MAX
            {
                (x + x) as u32
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Closed spec methods inside an impl block.
    #[test] test_exec_spec_impl_closed_method IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct Pair {
                pub x: u32,
                pub y: u32,
            }

            impl Pair {
                pub closed spec fn sum(&self) -> u32
                    recommends self.x + self.y <= u32::MAX
                {
                    (self.x + self.y) as u32
                }

                pub open spec fn max(&self) -> u32 {
                    if self.x >= self.y { self.x } else { self.y }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// `&&&` and `|||` (BigAnd / BigOr) inside impl method bodies and inside
    /// `recommends` clauses.
    #[test] test_exec_spec_impl_big_and_or IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct Triple {
                pub a: u32,
                pub b: u32,
                pub c: u32,
            }

            impl Triple {
                pub open spec fn all_small(&self) -> bool {
                    &&& self.a <= 10
                    &&& self.b <= 10
                    &&& self.c <= 10
                }

                pub open spec fn any_small(&self) -> bool {
                    ||| self.a <= 10
                    ||| self.b <= 10
                    ||| self.c <= 10
                }

                pub open spec fn well_formed(&self) -> u32
                    recommends
                        self.a <= 100,
                        self.b <= 100,
                        self.c <= 100,
                {
                    (self.a + self.b + self.c) as u32
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// `e is Variant` over user-defined enums with all three variant shapes
    /// (named, tuple, unit). Also `isnt`.
    #[test] test_exec_spec_is_user_enum IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub enum E {
                Named { v: u32 },
                Tuple(u32),
                Unit,
            }

            pub open spec fn classify(e: E) -> u32 {
                if e is Named {
                    1
                } else if e is Tuple {
                    2
                } else {
                    3
                }
            }

            pub open spec fn not_named(e: E) -> bool {
                e isnt Named
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// `e is Variant` on `Option`.
    #[test] test_exec_spec_is_option IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub open spec fn is_some(o: Option<u32>) -> bool {
                o is Some
            }

            pub open spec fn is_none(o: Option<u32>) -> bool {
                o is None
            }

            pub open spec fn not_some(o: Option<u32>) -> bool {
                o isnt Some
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests prefix deref `*self` in a spec method body (exercises `UnOp::Deref`).
    #[test] test_exec_spec_impl_deref_self IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            pub struct W { pub v: u32 }

            impl W {
                pub open spec fn copy(&self) -> W {
                    *self
                }
            }
        }

        fn sanity_check() {
            let w = ExecW { v: 7 };
            let c = w.exec_copy();
            assert(c.v == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_spec_match_guard IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn guarded(x: Option<u32>) -> u32 {
                match x {
                    Some(v) if v > 3 => v,
                    Some(_) => 0,
                    None => 1,
                }
            }

            enum E {
                A(u32),
                B { y: u32 },
            }

            spec fn guarded_enum(e: E, k: u32) -> bool {
                match e {
                    E::A(v) if v == k => true,
                    E::B { y } if y < k => true,
                    _ => false,
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_spec_impl_self_paths IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            struct P(u32);

            impl P {
                spec fn get(&self) -> u32 {
                    self.0
                }

                spec fn copy(&self) -> P {
                    Self(self.0)
                }

                spec fn get_via_self(&self) -> u32 {
                    Self::get(self)
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_spec_ext_eq_forms IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn ext_eq(a: Seq<u8>, b: Seq<u8>) -> bool {
                a =~= b
            }

            spec fn ext_ne(a: Seq<u8>, b: Seq<u8>) -> bool {
                (a) !~= b
            }

            spec fn big_eq(a: Seq<u8>, b: Seq<u8>) -> bool {
                a === b
            }

            spec fn big_ne(a: Seq<u8>, b: Seq<u8>) -> bool {
                (a) !== b
            }

            spec fn deep_eq(a: Seq<Seq<u8>>, b: Seq<Seq<u8>>) -> bool {
                a =~~= b
            }

            spec fn deep_ne(a: Seq<Seq<u8>>, b: Seq<Seq<u8>>) -> bool {
                (a) !~~= b
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_spec_is_variant_builtin IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            enum E {
                A(u32),
                B,
            }

            spec fn opt_is_some(o: Option<u32>) -> bool {
                is_variant(o, "Some")
            }

            spec fn opt_is_none(o: Option<u32>) -> bool {
                is_variant(o, "None")
            }

            spec fn enum_is_a(e: E) -> bool {
                is_variant(e, "A")
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_spec_arrow IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            struct Q {
                x: u32,
            }

            enum E {
                A(u32, Seq<u8>),
                B { x: u32, q: Q },
                C { x: u32, z: u32 },
                D,
            }

            spec fn opt_some_0(o: Option<u32>) -> u32
                recommends o is Some,
            {
                o->Some_0
            }

            spec fn opt_0(o: Option<u32>) -> u32
                recommends o is Some,
            {
                o->0
            }

            spec fn opt_struct(o: Option<Q>) -> Q
                recommends o is Some,
            {
                o->Some_0
            }

            spec fn tuple_field(e: E) -> Seq<u8>
                recommends e is A,
            {
                e->A_1
            }

            spec fn named_field(e: E) -> Q
                recommends e is B,
            {
                e->B_q
            }

            spec fn direct_field(e: E) -> u32
                recommends e is C,
            {
                e->z
            }

            spec fn direct_tuple_field(e: E) -> u32
                recommends e is A,
            {
                e->0
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_spec_arrow_requires_variant IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn opt_0(o: Option<u32>) -> u32 {
                o->0
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "precondition not satisfied")
}

test_verify_one_file! {
    #[test] test_exec_spec_fixed_width_arith IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn add_u8(a: u8, b: u8) -> u8 {
                add(a, b)
            }

            spec fn sub_u8(a: u8, b: u8) -> u8 {
                sub(a, b)
            }

            spec fn mul_u64(a: u64, b: u64) -> u64 {
                mul(a, b)
            }

            spec fn add_i32(a: i32, b: i32) -> i32 {
                add(a, b)
            }

            spec fn sub_i8(a: i8, b: i8) -> i8 {
                sub(a, b)
            }

            spec fn mul_isize(a: isize, b: isize) -> isize {
                mul(a, b)
            }

            spec fn sub_literal(t: u8) -> u8 {
                sub(8, t)
            }
        }

        fn test() {
            let a = exec_add_u8(2, 3);
            assert(a == 5);
            let s = exec_sub_literal(3);
            assert(s == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_spec_fixed_width_arith_user_fn IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn add(a: u8, b: u8) -> bool {
                a < b
            }

            spec fn uses_add(a: u8, b: u8) -> bool {
                add(a, b)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_spec_rejects_tracked_param IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn f(tracked x: u64) -> bool {
                x > 0
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`tracked` parameters are not supported")
}

test_verify_one_file! {
    #[test] test_exec_spec_rejects_let_tracked IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn f(x: u64) -> u64 {
                let tracked y = x;
                y
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`let tracked` is not supported")
}

test_verify_one_file! {
    #[test] test_exec_spec_rejects_let_ghost IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn f(x: u64) -> u64 {
                let ghost y = x;
                y
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`let ghost` is not supported")
}

test_verify_one_file! {
    #[test] test_exec_spec_rejects_tracked_struct IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            tracked struct Perm {
                x: u64,
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`tracked` datatypes are not supported")
}

test_verify_one_file! {
    #[test] test_exec_spec_rejects_tracked_enum IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            tracked enum Perm {
                A,
                B(u64),
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`tracked` datatypes are not supported")
}

test_verify_one_file! {
    #[test] test_exec_spec_rejects_tracked_field IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            enum E {
                A { tracked x: u64 },
                B,
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`tracked` fields are not supported")
}

test_verify_one_file! {
    #[test] test_exec_spec_rejects_ghost_field IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            struct S {
                x: u64,
                ghost g: u64,
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "explicit `ghost` field markers are not supported")
}

test_verify_one_file! {
    #[test] test_exec_spec_accepts_ghost_datatypes IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            ghost struct V {
                x: u64,
                y: bool,
            }

            ghost enum W {
                Uninit,
                Init(u64),
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_spec_rejects_real IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn f(x: real) -> bool {
                true
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Type cannot be compiled from spec code to exec code")
}

test_verify_one_file! {
    #[test] test_exec_spec_mem_contents IMPORTS.to_string() + verus_code_str! {
        use vstd::raw_ptr::MemContents;

        exec_spec_verified! {
            struct Cell {
                m: MemContents<u32>,
            }

            spec fn init_above(m: MemContents<u32>, k: u32) -> bool {
                m.is_init() && m.value() > k
            }

            spec fn uninit(m: MemContents<u32>) -> bool {
                m.is_uninit()
            }

            spec fn is_init(m: MemContents<u32>) -> bool {
                m is Init
            }

            spec fn isnt_init(m: MemContents<u32>) -> bool {
                m isnt Init
            }

            spec fn is_variant_init(m: MemContents<u32>) -> bool {
                is_variant(m, "Init")
            }

            spec fn value_via_arrow(m: MemContents<u32>) -> u32
                recommends m is Init,
            {
                m->0
            }

            spec fn rebuild(m: MemContents<u32>) -> MemContents<u32> {
                match m {
                    MemContents::Init(v) => MemContents::Init(v),
                    MemContents::Uninit => MemContents::Uninit,
                }
            }

            spec fn same(a: MemContents<u32>, b: MemContents<u32>) -> bool {
                a == b
            }

            spec fn cell_init(c: Cell) -> bool {
                c.m.is_init()
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_spec_result IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            struct R {
                r: Result<u32, bool>,
            }

            spec fn id(r: Result<u32, bool>) -> Result<u32, bool> {
                r
            }

            spec fn is_ok(r: Result<u32, bool>) -> bool {
                r is Ok
            }

            spec fn same(a: Result<u32, bool>, b: Result<u32, bool>) -> bool {
                a == b
            }

            spec fn ok_val(r: Result<u32, bool>) -> u32
                recommends r is Ok,
            {
                r->Ok_0
            }

            spec fn err_val(r: Result<u32, bool>) -> bool
                recommends r is Err,
            {
                r->Err_0
            }

            spec fn to_u32(r: Result<u32, bool>) -> u32 {
                match r {
                    Ok(v) => v,
                    Err(b) => if b { 1 } else { 0 },
                }
            }

            spec fn mk(v: u32) -> Result<u32, bool> {
                if v > 3 { Ok(v) } else { Err(false) }
            }

            spec fn field_ok(x: R) -> bool {
                x.r is Ok
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_exec_spec_type_macro IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            struct P {
                x: u32,
            }

            spec fn total(s: Seq<u32>, p: P, o: Option<u32>) -> (Seq<u32>, u32) {
                (s, p.x)
            }
        }

        fn call(
            s: exec_spec_type!(ref Seq<u32>),
            p: exec_spec_type!(ref P),
            o: exec_spec_type!(ref Option<u32>),
        ) -> (res: exec_spec_type!((Seq<u32>, u32)))
            ensures
                res.deep_view() == total(s.deep_view(), p.deep_view(), o.deep_view()),
        {
            exec_total(s, p, o)
        }

        fn owned(v: exec_spec_type!(Seq<u32>), m: exec_spec_type!(Map<u32, bool>)) -> (res: usize)
            ensures
                res == v.len(),
        {
            v.len()
        }
    } => Ok(())
}

//  Verifies `PointsTo` permission contracts via their
// `MemContents` view alongside runtime evaluation of the `ExecMemContents` mirror
test_verify_one_file! {
    #[test] test_exec_spec_pptr_permissions IMPORTS.to_string() + verus_code_str! {
        use vstd::raw_ptr::MemContents;
        use vstd::simple_pptr::{PPtr, PointsTo};

        exec_spec_verified! {
            struct TwoSlotPermView {
                slot_a: MemContents<u32>,
                slot_b: MemContents<u32>,
            }

            spec fn both_uninit(v: TwoSlotPermView) -> bool {
                v.slot_a is Uninit && v.slot_b.is_uninit()
            }

            spec fn sum_if_bounded(v: TwoSlotPermView, bound: u32) -> Result<u32, bool> {
                match v.slot_a {
                    MemContents::Init(a) if a <= bound => {
                        if v.slot_b is Init && v.slot_b->0 <= bound {
                            Ok(add(a, v.slot_b.value()))
                        } else {
                            Err(false)
                        }
                    }
                    MemContents::Init(_) => Err(true),
                    MemContents::Uninit => Err(false),
                }
            }
        }

        fn init_and_sum_slots(
            ptr_a: PPtr<u32>,
            ptr_b: PPtr<u32>,
            Tracked(pa): Tracked<&mut PointsTo<u32>>,
            Tracked(pb): Tracked<&mut PointsTo<u32>>,
        )
            requires
                old(pa).pptr() == ptr_a,
                old(pb).pptr() == ptr_b,
                both_uninit(TwoSlotPermView {
                    slot_a: old(pa).mem_contents(),
                    slot_b: old(pb).mem_contents(),
                }),
            ensures
                final(pa).pptr() == ptr_a,
                final(pb).pptr() == ptr_b,
                sum_if_bounded(TwoSlotPermView {
                    slot_a: final(pa).mem_contents(),
                    slot_b: final(pb).mem_contents(),
                }, 100) === Ok(30),
        {
            ptr_a.put(Tracked(pa), 10);
            ptr_b.put(Tracked(pb), 20);
        }

        fn test_exec_mirror() {
            let init_view: exec_spec_type!(TwoSlotPermView) = ExecTwoSlotPermView {
                slot_a: ExecMemContents::Init(10),
                slot_b: ExecMemContents::Init(20),
            };
            let res: exec_spec_type!(Result<u32, bool>) = exec_sum_if_bounded(&init_view, 100);
            assert(res.deep_view() === Ok(30u32));
        }
    } => Ok(())
}
