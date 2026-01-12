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

test_verify_one_file! {
  #[test] test_default_string_ok verus_code! {
    use vstd::prelude::*;
    fn test() {
      let a = String::default();
      assert(a@.len() == 0);
      assert(a.is_ascii());
    }
  } => Ok(())
}

test_verify_one_file! {
  #[test] test_default_vec_u32_ok verus_code! {
    use vstd::prelude::*;
    fn test() {
      let v: Vec<u32> = Vec::default();
      assert(v@.len() == 0);
    }
  } => Ok(())
}

test_verify_one_file! {
  #[test] test_default_hash_map_u32_ok verus_code! {
    use vstd::prelude::*;
    use std::collections::HashMap;
    fn test() {
      let m: HashMap<u32, u32> = HashMap::default();
      assert(m@.len() == 0);
    }
  } => Ok(())
}

test_verify_one_file! {
  #[test] test_default_hash_set_u32_ok verus_code! {
    use vstd::prelude::*;
    use std::collections::HashSet;
    fn test() {
      let s: HashSet<u32> = HashSet::default();
      assert(s@.len() == 0);
    }
  } => Ok(())
}

test_verify_one_file! {
  #[test] test_default_box_u32_ok verus_code! {
    use vstd::prelude::*;
    fn test() {
      let b: Box<u32> = Box::default();
      assert(*b == 0);
    }
  } => Ok(())
}

test_verify_one_file! {
  #[test] test_default_box_vec_u32_ok verus_code! {
    use vstd::prelude::*;
    fn test() {
      let b: Box<Vec<u32>> = Box::default();
      let v: Vec<u32> = *b;
      assert(v@.len() == 0);
    }
  } => Ok(())
}

test_verify_one_file! {
  #[test] test_default_rc_u32_ok verus_code! {
    use vstd::prelude::*;
    use std::rc::Rc;
    fn test() {
      let r: Rc<u32> = Rc::default();
      assert(*r == 0);
    }
  } => Ok(())
}

test_verify_one_file! {
  #[test] test_default_arc_u32_ok verus_code! {
    use vstd::prelude::*;
    use std::sync::Arc;
    fn test() {
      let a: Arc<u32> = Arc::default();
      assert(*a == 0);
    }
  } => Ok(())
}

test_verify_one_file! {
  #[test] test_default_vec_deque_u32_ok verus_code! {
    use vstd::prelude::*;
    use std::collections::VecDeque;
    fn test() {
      let v: VecDeque<u32> = VecDeque::default();
      assert(v@.len() == 0);
    }
  } => Ok(())
}

// more complex usages

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

    fn mk<T: Default>() -> (r: T)
        ensures
            T::default.ensures((), r),
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

// establish a simple determinstic value
test_verify_one_file! {
  #[test] test_default_custom_type_spec verus_code! {
    use vstd::prelude::*;

    pub struct MyType {
        pub x: u32,
        pub y: bool,
    }

    impl Default for MyType {
        fn default() -> (r: MyType)
            ensures
                r.x == 10,
                r.y == true,
        {
            MyType { x: 10, y: true }
        }
    }

    fn mk() -> (r: MyType)
        ensures
            r.x == 10,
            r.y == true,
    {
        MyType::default()
    }

    fn test() {
        let v = mk();
        assert(v.x == 10);
        assert(v.y == true);
    }
  } => Ok(())
}

// establish arbitrary default ensures for custom types, and use it in smart pointers
test_verify_one_file! {
  #[test] test_default_custom_type_ensures_in_smart_ptrs verus_code! {
    use vstd::prelude::*;
    use std::rc::Rc;
    use std::sync::Arc;

    pub struct MyType {
        pub x: u32,
        pub y: u32,
    }

    impl Default for MyType {
        fn default() -> (r: MyType)
            ensures
                r.y == r.x + 1,
                r.x < 100,
        {
            MyType { x: 7, y: 8 }
        }
    }

    fn test() {
      let b: Box<MyType> = Box::default();
      assert((*b).y == (*b).x + 1);
      assert((*b).x < 100);

      let r: Rc<MyType> = Rc::default();
      assert((*r).y == (*r).x + 1);
      assert((*r).x < 100);

      let a: Arc<MyType> = Arc::default();
      assert((*a).y == (*a).x + 1);
      assert((*a).x < 100);
    }
  } => Ok(())
}
