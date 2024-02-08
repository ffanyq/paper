use std::ptr::addr_of;
use std::sync::Arc;

fn foo(mut a: *const i32, mut b: *const i32, mut c: *const i32) -> *const i32 {

    let mut d  = 4;
    //let ptr = &d as *const String;
    //let t = String::from_raw_parts(ptr);
    a = b;
    b = c;
    a = addr_of!(d);

    a
}
fn main() {

    let mut a = 1;
    let mut b = 2;
    let mut c = 3;
    let mut m = 5;

    let mut pa =  addr_of!(a);
    let mut pb =  addr_of!(b);
    let mut pc =  addr_of!(c);
    let mut pm =  addr_of!(m);

    pa = pm;
    pb = pa;
    pm = pc;
    //let t = *a;
    let mut e = foo(pa, pb, pc);
    //e = pm

}