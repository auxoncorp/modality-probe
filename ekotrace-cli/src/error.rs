use std::{fmt::Display, process::exit};

#[macro_export]
macro_rules! exit_error {
    ($msg:expr) => ({
        eprintln!($msg);
        std::process::exit(1);
    });
    ($msg:expr,) => ({
        $crate::exit_error!($msg)
    });
    ($fmt:expr, $($arg:tt)+) => ({
        eprintln!($fmt, $($arg)*);
        std::process::exit(1);
    });
}

pub(crate) trait GracefulExit<T> {
    fn unwrap_or_exit(self, msg: &str) -> T;
}

impl<T> GracefulExit<T> for Option<T> {
    fn unwrap_or_exit(self, msg: &str) -> T {
        self.unwrap_or_else(|| {
            eprintln!("{}", msg);
            exit(1);
        })
    }
}

impl<T, E: Display> GracefulExit<T> for Result<T, E> {
    fn unwrap_or_exit(self, msg: &str) -> T {
        self.unwrap_or_else(|e| {
            eprintln!("{}\nCause:\n  {}", msg, e);
            exit(1);
        })
    }
}
