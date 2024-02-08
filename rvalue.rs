use std::ptr::addr_of;
pub enum Foo {
    Apple,
    Pear,
    Banana,
}

pub struct S {
    pub x: i32,
    pub y: i32,
}
fn main() {
    let a:i32 = 10;//Use

    let d = "as";
    let ref_a = &a;//Ref

    let b = String::from("abc");
    //let move_b = b;//Use

    let c = [2; 3];//Repeat
    let ref_c = &c;//Ref

    let addr_b = &b as *const String;//Ref + AddressOf
    let addr_of_b = addr_of!(b);

    let as_ptr_b = b.as_ptr();//Ref

    let len_b = b.len();//Ref

    let cast_mut_b = addr_b as *mut String;//Cast

    let binary_a = a > 2;//Use + BinaryOp
    let UnaryOp_a = a >> 2;//Use + Cast + BinaryOp + BinaryOp

    let d = Foo::Banana;//Aggregate

    match d {//Discriminant
        Foo::Apple => {}
        Foo::Pear => {}
        Foo::Banana => {}
    }
    let mut e = S{x: 1, y: 2};//Aggregate

    e.x = 3;//Use

    let mut g = Vec::new();
    g.push(2);//Ref

    let box_g = unsafe { Box::from_raw(g.as_mut_ptr()) };//Ref

}

