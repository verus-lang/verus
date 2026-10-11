fn test(a: *mut [*mut [*mut u64]; 20], b: *mut u8, c: *mut u8) {
    unsafe {
        let x = *(*(*a)[{ let y = 13; 0 }])[11];
    }
}

 fn main() { }
