use std::{fmt::Display, process::exit};

#[macro_export]
macro_rules! warn {
    ($prefix:expr, $tag:expr, $msg:expr) => {{
        eprintln!("{} {}: warning: {}", $prefix, $tag, $msg);
    }};
     ($prefix:expr, $tag:expr, $fmt:expr, $($arg:tt)+) => ({
        eprint!("{} {}: warning: ", $prefix, $tag);
        eprintln!($fmt, $($arg)*);
    });
}

#[macro_export]
macro_rules! exit_error {
    ($prefix:expr, $tag:expr, $msg:expr) => {{
        eprintln!("{} {}: error: {}", $prefix, $tag, $msg);
        std::process::exit(1);
    }};
     ($prefix:expr, $tag:expr, $fmt:expr, $($arg:tt)+) => ({
        eprint!("{} {}: error: ", $prefix, $tag);
        eprintln!($fmt, $($arg)*);
        std::process::exit(1);
    });
}

pub(crate) trait GracefulExit<T> {
    fn unwrap_or_exit(self, msg: &str) -> T;
}

impl<T, E: Display> GracefulExit<T> for Result<T, E> {
    fn unwrap_or_exit(self, msg: &str) -> T {
        self.unwrap_or_else(|e| {
            eprintln!("ekotrace {}: error: {}", msg, e);
            exit(1);
        })
    }
}
