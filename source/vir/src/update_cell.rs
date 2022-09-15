pub struct UpdateCell<T> {
    contents: Option<T>,
}

impl<T> UpdateCell<T> {
    pub fn new(t: T) -> Self {
        Self { contents: Some(t) }
    }

    pub fn borrow(&self) -> &T {
        self.contents.as_ref().unwrap()
    }

    pub fn borrow_mut(&mut self) -> &mut T {
        self.contents.as_mut().unwrap()
    }

    pub fn update<O>(&mut self, f: impl FnOnce(T) -> (T, O)) -> O {
        let t = self.contents.take().unwrap();
        let (t, o) = f(t);
        self.contents = Some(t);
        o
    }
}
