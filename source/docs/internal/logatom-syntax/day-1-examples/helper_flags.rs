use std::sync::atomic::*;

pub struct FlagTracker {
    flag: AtomicBool,
    channel: AtomicU32,
}

impl FlagTracker {
    pub fn new() -> Self {
        FlagTracker {
            flag: AtomicBool::new(false),
            channel: AtomicU32::new(0),
        }
    }

    pub fn read(&self) -> bool {
        self.flag.load(Ordering::SeqCst)
    }

    pub fn flip(&self) {
        loop {
            if self.channel.compare_exchange(1, 2, Ordering::SeqCst, Ordering::SeqCst).is_ok() {
                return;
            }

            if self.flag.compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst).is_ok() {
                return;
            }

            if self.flag.compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst).is_ok() {
                return;
            }

            if self.channel.compare_exchange(0, 1, Ordering::SeqCst, Ordering::SeqCst).is_ok() {
                if self.channel.compare_exchange(1, 0, Ordering::SeqCst, Ordering::SeqCst).is_ok() {
                    // try again
                    continue;
                } else {
                    self.channel.store(0, Ordering::SeqCst);
                }
            }
        }
    }
}

fn main() {
    let f = FlagTracker::new();
    dbg!(f.read());
    f.flip();
    dbg!(f.read());
    f.flip();
    dbg!(f.read());
}
