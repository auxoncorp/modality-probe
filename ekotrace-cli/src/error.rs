use std::{fmt::Display, process::exit};

#[macro_export]
macro_rules! warn {
    ($tag:expr, $msg:expr) => {{
        eprintln!("ekotrace {}: warning: {}", $tag, $msg);
    }};
     ($tag:expr, $fmt:expr, $($arg:tt)+) => ({
        eprint!("ekotrace {}: warning: ", $tag);
        eprintln!($fmt, $($arg)*);
    });
}

#[macro_export]
macro_rules! exit_error {
    ($tag:expr, $msg:expr) => {{
        eprintln!("ekotrace {}: error: {}", $tag, $msg);
        std::process::exit(1);
    }};
     ($tag:expr, $fmt:expr, $($arg:tt)+) => ({
        eprint!("ekotrace {}: error: ", $tag);
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
