use std::{thread, sync::Arc};
use std::sync::Mutex;
fn foo() {
    let a = 10;
}
fn main() {
    foo();
    let mut v = 0;
    let m = Arc::new(Mutex::new(v));
    let clone = m.clone();

    let t1 = thread::spawn(move || unsafe {
        let ptr;
        {
            let mut t = clone.lock().unwrap();
            ptr = &mut *t as *mut i32;
        }
        (*ptr) += 1;
    });

    let clone2 = m.clone();
    let t2 = thread::spawn(move || unsafe {
        let ptr;
        {
            let mut t = clone2.lock().unwrap();
            ptr = &mut *t as *mut i32;
        }
        (*ptr) += 1;
    });

    t1.join().unwrap();
    t2.join().unwrap();
    println!("{:?}", m.lock().unwrap());
}
