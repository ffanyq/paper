//! The general rustc plugin framework.
//! Inspired by <https://github.com/facebookexperimental/MIRAI/blob/9cf3067309d591894e2d0cd9b1ee6e18d0fdd26c/checker/src/main.rs>
#![feature(rustc_private)]
#![feature(box_patterns)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
mod callback;
mod analyzer;
fn main() {
    let args: Vec<String> = vec![
        "rustc".to_string(), // 通常第一个参数是可执行文件名
        "toy.rs".to_string(), // 指定要编译的 Rust 源文件
    ];

    let result = rustc_driver::catch_fatal_errors(|| {
        let mut callbacks = callback::rlock_callback;
        let compiler =
        rustc_driver::RunCompiler::new(&args.as_slice(), &mut callbacks);
        compiler.run()

    }).and_then(|result| result);

    
    let exit_code = match result {
        Ok(_) => rustc_driver::EXIT_SUCCESS,
        Err(_) => rustc_driver::EXIT_FAILURE,
    };
    std::process::exit(exit_code);
}
