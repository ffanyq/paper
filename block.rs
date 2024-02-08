#![feature(rustc_private)]
extern crate rand;
use rand::Rng;

fn foo(v : i32) -> i32{
    v + 1
}
fn main() {
    let mut rng = rand::thread_rng();
    let random_number = rng.gen_range(1..=10);
    let mut a = 10;
    if(random_number > 5) {
        a = foo(a);
    }
    else {
        a = foo(a + 1);
    }
}