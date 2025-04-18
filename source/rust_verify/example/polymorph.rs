use builtin::*;
use builtin_macros::*;


verus! {
	spec fn spec0(n: int) -> int {
		n + n
	}
	spec fn spec1<A>(a: A) -> A {
		a
	}

	proof fn proof1<A>(b: A) {
		let flag = spec1(true);
		let _obj = spec1(b);
	}
}

fn main()
{

}
