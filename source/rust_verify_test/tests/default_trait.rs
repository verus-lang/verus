#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// simple tests

macro_rules! test_default_ok {
    ($name:ident, $ty:ty, $expected:expr) => {
        test_verify_one_file! {
          #[test] $name format!(r#"
        ::verus_builtin_macros::verus! {{
          use vstd::prelude::*;

          fn test() {{
            let a = <{ty}>::default();
            let b: {ty} = Default::default(); // inference
            let c = <{ty} as core::default::Default>::default();  // UFCS
            assert(a == {expected});
            assert(b == {expected});
            assert(c == {expected});
          }}
        }}
      "#, ty = stringify!($ty), expected = stringify!($expected)) => Ok(())
        }
    };
}

macro_rules! test_default_fail {
    ($name:ident, $ty:ty, $wrong:expr) => {
        test_verify_one_file! {
          #[test] $name format!(r#"
        ::verus_builtin_macros::verus! {{
          use vstd::prelude::*;
          fn test() {{
            let x = <{ty}>::default();
            assert(x == {wrong}); // FAILS
          }}
        }}
      "#, ty = stringify!($ty), wrong = stringify!($wrong)) => Err(e) => assert_one_fails(e)
        }
    };
}

test_default_ok!(test_default_u32_ok, u32, 0u32);
test_default_fail!(test_default_u32_wrong, u32, 1u32);
test_default_ok!(test_default_bool_ok, bool, false);
test_default_fail!(test_default_bool_wrong, bool, true);
test_default_ok!(test_default_f32_ok, f32, 0.0f32);
test_default_ok!(test_default_f64_ok, f64, 0.0f64);
test_default_ok!(test_default_str_ok, &'static str, "");
test_default_ok!(test_default_option_u32_ok, Option<u32>, Option::<u32>::None);
test_default_ok!(
    test_default_phantom_ok,
    core::marker::PhantomData<u32>,
    core::marker::PhantomData::<u32>
);
test_default_ok!(test_default_tuple2_ok, (u32, bool), (0u32, false));
test_default_ok!(test_default_tuple3_ok, (u32, bool, char), (0u32, false, '\0'));

// more complex usages

test_verify_one_file! {
  #[test] test_default_u32_through_wrapper verus_code! {
    use vstd::prelude::*;
    use core::default::Default;

    fn wrap() -> (r: u32)
      ensures r == 0
    {
      <u32 as Default>::default()
    }

    fn test() {
      let x = wrap();
      assert(x == 0);
    }
  } => Ok(())
}

test_verify_one_file! {
    #[test] test_default_in_struct verus_code! {
        use vstd::prelude::*;

        struct MyStruct {
            x: u32,
            y: bool,
        }

        fn create_with_defaults() -> (r: MyStruct)
            ensures r.x == 0 && r.y == false
        {
            MyStruct {
                x: u32::default(),
                y: bool::default(),
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_default_arithmetic verus_code! {
        use vstd::prelude::*;

        fn test() {
            let x = u32::default();
            let y = x + 5;
            assert(y == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
  #[test] test_default_generic_instantiation verus_code! {
    use vstd::prelude::*;
    use core::default::Default;
    use vstd::std_specs::core::DefaultSpec;

    fn mk<T: Default>() -> (r: T)
        ensures T::obeys_default_spec() ==> r == T::default_spec()
    {
      T::default()
    }

    fn test() {
      let x: u32 = mk::<u32>();
      let y: bool = mk::<bool>();
      assert(x == 0);
      assert(y == false);
    }
  } => Ok(())
}
