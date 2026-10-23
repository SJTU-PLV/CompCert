use crate::ptr::Ptr;

extern "C" {
    #[link_name = "printf"]
    pub(crate) fn __libc_printf(fmt: *const i8, ...) -> i32;
}

/// Safe wrapper for `printf(fmt)` (no variadic arguments).
pub fn print_c_string(fmt: Ptr<i8>) -> i32 {
    unsafe { __libc_printf(fmt.as_ptr()) }
}

/// Best-effort replacement for `scanf("%d", &mut x)` used by the translator.
///
/// Semantics: returns the first whitespace-delimited `i32` from stdin; returns
/// `default` if parsing fails or stdin is empty.
pub fn read_i32_with_default(default: i32) -> i32 {
    use std::io::BufRead;

    let mut input = String::new();
    if std::io::stdin().lock().read_line(&mut input).is_err() {
        return default;
    }
    for token in input.split_whitespace() {
        if let Ok(value) = token.parse::<i32>() {
            return value;
        }
    }
    default
}

/// Call C `printf` without writing `unsafe` in generated code.
///
/// The `unsafe` boundary stays inside the runtime.
#[macro_export]
macro_rules! c_printf {
    ($fmt:expr $(, $arg:expr)* $(,)?) => {{
        unsafe { $crate::stdio::__libc_printf(($fmt).as_ptr() $(, $arg )* ) }
    }};
}
