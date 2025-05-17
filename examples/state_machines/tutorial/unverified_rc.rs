// rust_verify/tests/example.rs ignore --- ordinary rust, not verus

// ANCHOR: full
// Ordinary Rust code, not Verus

struct InnerRc<T> {
    rc_cell: std::cell::UnsafeCell<u64>,
    t: T,
}

struct Rc<T> {
    ptr: *mut InnerRc<T>,
}

impl<T> Rc<T> {
    fn new(t: T) -> Self {
        // Allocate a new InnerRc object, initialize the counter to 1,
        // and return a pointer to it.
        let rc_cell = std::cell::UnsafeCell::new(1);
        let inner_rc = InnerRc { rc_cell, t };
        let ptr = Box::leak(Box::new(inner_rc));
        Rc { ptr }
    }

    fn clone(&self) -> Self {
        unsafe {
            // Increment the counter.
            // If incrementing the counter would lead to overflow, then abort.
            let inner_rc = &*self.ptr;
            let count = *inner_rc.rc_cell.get();
            if count == 0xffffffffffffffff {
                std::process::abort();
            }
            *inner_rc.rc_cell.get() = count + 1;
        }

        // Return a new Rc object with the same pointer.
        Rc { ptr: self.ptr }
    }

    fn drop(self) {
        unsafe {
            // Decrement the counter.
            let inner_rc = &*self.ptr;
            let count = *inner_rc.rc_cell.get() - 1;
            *inner_rc.rc_cell.get() = count;

            // If the counter hits 0, drop the `T` and deallocate the memory.
            if count == 0 {
                std::ptr::drop_in_place(&mut (*self.ptr).t);
                std::alloc::dealloc(self.ptr as *mut u8, std::alloc::Layout::for_value(&*self.ptr));
            }
        }
    }

    fn borrow(&self) -> &T {
        unsafe { &(*self.ptr).t }
    }
}

// Example usage

enum Sequence<V> {
    Nil,
    Cons(V, Rc<Sequence<V>>),
}

fn main() {
    let nil = Rc::new(Sequence::Nil);
    let nil_clone = nil.clone();
    let a5 = Rc::new(Sequence::Cons(5, nil.clone()));
    let a7 = Rc::new(Sequence::Cons(7, nil.clone()));
    let a67 = Rc::new(Sequence::Cons(6, a7.clone()));

    let x1 = nil.borrow();
    let x2 = nil_clone.borrow();
    match x1 {
        Sequence::Nil => {}
        Sequence::Cons(_, _) => {
            assert!(false);
        }
    }
    match x2 {
        Sequence::Nil => {}
        Sequence::Cons(_, _) => {
            assert!(false);
        }
    }

    nil.drop();
    nil_clone.drop();
    a5.drop();
    a7.drop();
    a67.drop();
}
// ANCHOR_END: full
