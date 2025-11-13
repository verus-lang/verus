use vstd::prelude::*;

verus! {
    pub open spec fn ex_saturating_sub_spec(a: int, b: int) -> (ret: nat)
    {
        if (a > b) {
            (a - b) as nat
        } else {
            0
        }
    }

    #[verifier::external_fn_specification]
    pub fn ex_saturating_sub(a: usize, b: usize) -> (ret: usize)
    ensures
        ex_saturating_sub_spec(a as int, b as int) == ret as int
    {
        a.saturating_sub(b)
    }

    pub struct RingBuffer<T: Copy> {
        ring: Vec<T>,
        head: usize,
        tail: usize,
    }

    impl<T: Copy> View for RingBuffer<T> {
        type V = (Seq<T>, usize);

        closed spec fn view(&self) -> Self::V {
            let cap = self.ring.len();
            if self.tail >= self.head {
                ((self.ring)@.subrange(self.head as int, self.tail as int),
                cap)
            } else {
                ((self.ring)@.subrange(self.head as int, cap as int)
                    .add((self.ring)@.subrange(0, self.tail as int)),
                    cap)
            }
        }
    }

    /// This function says that for any `x` and `y`, there are two
    /// possibilities for the sum `x % n + y % n`:
    /// (1) It's in the range `[0, n)` and equals `(x + y) % n`.
    /// (2) It's in the range `[n, 2n)` and equals `(x + y) % n + n`.
    pub open spec fn mod_auto_plus(n: int) -> bool
        recommends
            n > 0,
    {
        forall|x: int, y: int|
            {
                let z = (x % n) + (y % n);
                ((0 <= z < n && #[trigger] ((x + y) % n) == z)
                    || (n <= z < n + n && ((x + y) % n) == z - n))
            }
    }

    /// This function says that for any `x` and `y`, there are two
    /// possibilities for the difference `x % n - y % n`:
    /// (1) It's in the range `[0, n)` and equals `(x - y) % n`.
    /// (2) It's in the range `[-n, 0)` and equals `(x - y) % n - n`.
    pub open spec fn mod_auto_minus(n: int) -> bool
        recommends
            n > 0,
    {
        forall|x: int, y: int|
            {
                let z = (x % n) - (y % n);
                ((0 <= z < n && #[trigger] ((x - y) % n) == z)
                    || (-n <= z < 0 && ((x - y) % n) == z + n))
            }
    }

    /// This function states various useful properties about the modulo
    /// operator when the divisor is `n`.
    pub open spec fn mod_auto(n: int) -> bool
        recommends
            n > 0,
    {
        &&& (n % n == 0 && (-n) % n == 0)
        &&& (forall|x: int| #[trigger] ((x % n) % n) == x % n)
        &&& (forall|x: int| 0 <= x < n <==> #[trigger] (x % n) == x)
        &&& mod_auto_plus(n)
        &&& mod_auto_minus(n)
    }

    /// Proof of `mod_auto(n)`, which states various useful properties
    /// about the modulo operator when the divisor is the positive
    /// number `n`
    pub proof fn lemma_mod_auto(n: int)
        requires
            n > 0,
        ensures
            mod_auto(n),
    {
        admit()
    }


#[verifier::external_body]
fn my_set<T: Copy>(vec: &mut Vec<T>, i: usize, value: T)
    requires
        i < old(vec).len(),
    ensures
        vec@ == old(vec)@.update(i as int, value),
        vec@.len() == old(vec).len()
        no_unwind
{
    vec[i] = value;
}


impl<T: Copy> RingBuffer<T> {
    /// Invariant for the ring buffer.
    #[verifier::type_invariant]
    closed spec fn inv(&self) -> bool {
        &&& self.head < self.ring.len()
        &&& self.tail < self.ring.len()
        &&& self.ring.len() > 0
    }


    /// Returns how many elements are in the buffer.
    pub fn len(&self) -> (ret: usize)
        ensures
            ret == self@.0.len(),
    {
        proof {
            use_type_invariant(&self);
            lemma_mod_auto(self@.1 as int);
        }
        if self.tail > self.head {
            self.tail - self.head
        } else if self.tail < self.head {
            (self.ring.len() - self.head) + self.tail
        } else {
            0
        }
    }

    /// Returns true if there are any items in the buffer, false otherwise.
    pub fn has_elements(&self) -> (ret: bool)
        ensures
            ret == (self@.0.len() != 0),
            true
    {
        proof {
            use_type_invariant(&self);
        }
        self.head != self.tail
    }

    pub closed spec fn ring_len(&self) -> usize {
        self.ring.len()
    }

    /// Returns true if the buffer is full, false otherwise.
    pub fn is_full(&self) -> (ret: bool)
    ensures
        ret == (self@.0.len() == (self@.1 - 1) as nat)
    {
        proof {
            use_type_invariant(&self);
            lemma_mod_auto(self@.1 as int);
        }
        self.head == ((self.tail + 1) % self.ring.len())
    }

    /// Creates a new RingBuffer with the given backing `ring` storage.
    pub fn new(ring: Vec<T>) -> (ret: RingBuffer<T>)
        requires
            ring.len() >= 1
        ensures
            ret@.0.len() == 0,
            ret@.1 == ring.len()
    {
        proof {
            assert(ring.len() >= 1);
        }
        RingBuffer {
            head: 0,
            tail: 0,
            ring,
        }
    }


    /// This method attempts to add a new element to the back of the ring buffer.
    /// The operation succeeds only if the buffer is not full.
    ///
    /// # Arguments
    /// * `val` - The value to add to the buffer
    ///
    /// # Returns
    /// * `true` - If the element was successfully added (buffer was not full)
    /// * `false` - If the element could not be added (buffer was full)
    ///
    /// # Invariants
    /// * The ring buffer's capacity remains unchanged
    /// * If successful, the length increases by 1 and the new value is at the end
    /// * If unsuccessful, the buffer remains unchanged
    /// * All previously enqueued elements remain in their original positions
    pub fn enqueue(&mut self, val: T) -> (succ: bool)
        ensures
            // Full fails iff old(len) == capacity => !succ
            old(self)@.0.len() == (old(self)@.1 - 1) as nat <==> !succ,
            // The ring size itself doesn't change:
            self@.1 == old(self)@.1,
            // If succ, length increments by 1:
            succ == (self@.0.len() == old(self)@.0.len() + 1),
            // The newly enqueued value is at the end:
            succ ==> (self@.0.last() == val),
            !succ ==> (self@ == old(self)@),
            // Previous elements unchanged:
            forall |i: int|
                0 <= i < old(self)@.0.len() ==> self@.0[i] == old(self)@.0[i]
    {
        if self.is_full() {
            false
        } else {
            proof {
                use_type_invariant(&*self);
                lemma_mod_auto(self@.1 as int);
            }
            my_set(&mut self.ring, self.tail, val);
            self.tail = (self.tail + 1) % self.ring.len();
            true
        }
    }

    /// Removes and returns the front element from the ring buffer, if one exists.
    ///
    /// This method attempts to remove and return the oldest element (front) from the buffer.
    /// If the buffer is empty, it returns None.
    ///
    /// # Returns
    /// * `Some(T)` - The front element if the buffer was not empty
    /// * `None` - If the buffer was empty
    pub fn dequeue(&mut self) -> (ret: Option<T>)
        ensures
            // The ring size remains unchanged
            self@.1 == old(self)@.1,
            // Empty fails
            old(self)@.0.len() == 0 <==> ret == None::<T>,
            old(self)@.0.len() > 0 <==> ret != None::<T>,

            if let Some(val) = ret {
                &&& self@.0.len() == old(self)@.0.len() - 1
                &&& val == old(self)@.0.first()
                &&& forall |i: int| 0 <= i < old(self)@.0.len() - 1 ==> self@.0[i] == old(self)@.0[i+1]
            } else {
                &&& self@.0.len() == old(self)@.0.len()
                &&& forall |i: int| 0 <= i < old(self)@.0.len() ==> self@.0[i] == old(self)@.0[i]
            }
    {
        proof {
            use_type_invariant(&*self);
            lemma_mod_auto(self@.1 as int);
        }

        if self.has_elements() {
            let val = self.ring[self.head];
            self.head = (self.head + 1) % self.ring.len();
            Some(val)
        } else {
            None
        }
    }



    /// Returns the number of elements that can still be enqueued until it is full.
    pub fn available_len(&self) -> (ret: usize)
    ensures ret == self@.1 - self@.0.len() - 1
    {
        proof {
            use_type_invariant(&self);
        }
        self.ring.len().saturating_sub(1 + self.len())
    }
}

/* TEST CODE BELOW */

#[verifier::loop_isolation(false)]
fn test1(len: usize, value: i32, iterations: usize)
    requires
        1 < len < usize::MAX - 1,
        iterations * 2 < usize::MAX,
{
    let mut ring: Vec<i32> = Vec::new();

    if len == 0 {
        return;
    }

    for i in 0..(len + 1)
    invariant
        ring.len() == i,
    {
        ring.push(0);
    }

    // assert(ring.len() == len + 1);
    let mut buf = RingBuffer::new(ring);

    let ret = buf.dequeue();
    let buf_len = buf.len();
    let has_elements = buf.has_elements();
    // assert(!has_elements);
    // assert(ret == None::<i32>);
    // assert(buf_len == 0);
    // assert(len > 1);
    for i in 0..len
    invariant
        buf@.0.len() == i,
        buf@.1 == len + 1
    {
        let enqueue_res = buf.enqueue(value);
        // assert(enqueue_res);
        let has_elements = buf.has_elements();
        // assert(has_elements);
        let available_len = buf.available_len();
        // assert(available_len == len - 1 - i);
    }
    let dequeue_res = buf.dequeue();
    // assert(dequeue_res.is_some());
    let enqueue_res = buf.enqueue(value);
    // assert(enqueue_res);
    let enqueue_res = buf.enqueue(value);
    // assert(!enqueue_res);
    let dequeue_res = buf.dequeue();
    // assert(dequeue_res.is_some());
}

#[verifier::loop_isolation(false)]
fn test2(len: usize, value: i32, iterations: usize)
    requires
        1 < len < usize::MAX - 1,
        iterations * 2 < usize::MAX,
{
    let mut ring: Vec<i32> = Vec::new();

    if len == 0 {
        return;
    }

    for i in 0..(len + 1)
    invariant
        ring.len() == i,
    {
        ring.push(0);
    }

    assert(ring.len() == len + 1);
    let mut buf = RingBuffer::new(ring);

    let ret = buf.dequeue();
    let buf_len = buf.len();
    let has_elements = buf.has_elements();
    assert(!has_elements);
    assert(ret == None::<i32>);
    assert(buf_len == 0);
    assert(len > 1);
    for i in 0..len
    invariant
        buf@.0.len() == i,
        buf@.1 == len + 1
    {
        let enqueue_res = buf.enqueue(value);
        // assert(enqueue_res);
        let has_elements = buf.has_elements();
        // assert(has_elements);
        let available_len = buf.available_len();
        // assert(available_len == len - 1 - i);
    }
    let dequeue_res = buf.dequeue();
    // assert(dequeue_res.is_some());
    let enqueue_res = buf.enqueue(value);
    // assert(enqueue_res);
    let enqueue_res = buf.enqueue(value);
    // assert(!enqueue_res);
    let dequeue_res = buf.dequeue();
    // assert(dequeue_res.is_some());
}

#[verifier::loop_isolation(false)]
fn test3(len: usize, value: i32, iterations: usize)
    requires
        1 < len < usize::MAX - 1,
        iterations * 2 < usize::MAX,
{
    let mut ring: Vec<i32> = Vec::new();

    if len == 0 {
        return;
    }

    for i in 0..(len + 1)
    invariant
        ring.len() == i,
    {
        ring.push(0);
    }

    assert(ring.len() == len + 1);
    let mut buf = RingBuffer::new(ring);

    let ret = buf.dequeue();
    let buf_len = buf.len();
    let has_elements = buf.has_elements();
    assert(!has_elements);
    assert(ret == None::<i32>);
    assert(buf_len == 0);
    assert(len > 1);
    for i in 0..len
    invariant
        buf@.0.len() == i,
        buf@.1 == len + 1
    {
        let enqueue_res = buf.enqueue(value);
        assert(enqueue_res);
        let has_elements = buf.has_elements();
        assert(has_elements);
        let available_len = buf.available_len();
        assert(available_len == len - 1 - i);
    }
    let dequeue_res = buf.dequeue();
    // assert(dequeue_res.is_some());
    let enqueue_res = buf.enqueue(value);
    // assert(enqueue_res);
    let enqueue_res = buf.enqueue(value);
    // assert(!enqueue_res);
    let dequeue_res = buf.dequeue();
    // assert(dequeue_res.is_some());
}

#[verifier::loop_isolation(false)]
fn test4(len: usize, value: i32, iterations: usize)
    requires
        1 < len < usize::MAX - 1,
        iterations * 2 < usize::MAX,
{
    let mut ring: Vec<i32> = Vec::new();

    if len == 0 {
        return;
    }

    for i in 0..(len + 1)
    invariant
        ring.len() == i,
    {
        ring.push(0);
    }

    assert(ring.len() == len + 1);
    let mut buf = RingBuffer::new(ring);

    let ret = buf.dequeue();
    let buf_len = buf.len();
    let has_elements = buf.has_elements();
    assert(!has_elements);
    assert(ret == None::<i32>);
    assert(buf_len == 0);
    assert(len > 1);
    for i in 0..len
    invariant
        buf@.0.len() == i,
        buf@.1 == len + 1
    {
        let enqueue_res = buf.enqueue(value);
        assert(enqueue_res);
        let has_elements = buf.has_elements();
        assert(has_elements);
        let available_len = buf.available_len();
        assert(available_len == len - 1 - i);
    }
    let dequeue_res = buf.dequeue();
    assert(dequeue_res.is_some());
    let enqueue_res = buf.enqueue(value);
    assert(enqueue_res);
    let enqueue_res = buf.enqueue(value);
    assert(!enqueue_res);
    let dequeue_res = buf.dequeue();
    assert(dequeue_res.is_some());
}

pub fn main() {
}
}
