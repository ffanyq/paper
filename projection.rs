#[derive(Clone)]
pub struct foo {
    x: i32,
    y: usize,
}
fn main() {
    let mut a = &foo { x: 1, y: 2};
    let t = &foo { x: 1, y: 3};
    a = t;
    let b = a.x;
    // let my_number = foo{x: 1, y: 2};

    // // 创建一个对 my_number 的引用
    // let my_reference = &my_number;

    // // 使用解引用符号来获取引用指向的值
    // let b = my_reference.x;
}