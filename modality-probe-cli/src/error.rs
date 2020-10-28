use std::{fmt::Display, process::exit};

use err_derive::Error;

#[macro_export]
macro_rules! warn {
    ($tag:expr, $msg:expr) => {{
        eprintln!("modality-probe {}: warning: {}", $tag, $msg);
    }};
     ($tag:expr, $fmt:expr, $($arg:tt)+) => ({
        eprint!("modality-probe {}: warning: ", $tag);
        eprintln!($fmt, $($arg)*);
    });
}

#[macro_export]
macro_rules! exit_error {
    ($tag:expr, $msg:expr) => {{
        eprintln!("modality-probe {}: error: {}", $tag, $msg);
        std::process::exit(1);
    }};
    ($tag:expr, $fmt:expr, $($arg:tt)+) => ({
        eprint!("modality-probe {}: error: ", $tag);
        eprintln!($fmt, $($arg)*);
        std::process::exit(1);
    });
}

pub trait GracefulExit<T> {
    fn unwrap_or_exit(self, msg: &str) -> T;
}

impl<T, E: Display> GracefulExit<T> for Result<T, E> {
    fn unwrap_or_exit(self, msg: &str) -> T {
        self.unwrap_or_else(|e| {
            eprintln!("modality-probe {}: error: {}", msg, e);
            exit(1);
        })
    }
}

impl<T> GracefulExit<T> for Option<T> {
    fn unwrap_or_exit(self, msg: &str) -> T {
        self.unwrap_or_else(|| {
            eprintln!("modality-probe error: {}", msg);
            exit(1);
        })
    }
}

/// A generic, message-driven error type.
#[derive(Debug, Error)]
#[error(display = "{}", msg)]
pub struct CmdError {
    pub msg: String,
    pub src: Option<Box<dyn std::error::Error>>,
}

impl From<String> for CmdError {
    fn from(msg: String) -> Self {
        CmdError { msg, src: None }
    }
}

#[macro_export]
macro_rules! give_up {
    ($msg:expr) => {
        return Err(Box::new($crate::error::CmdError {
            msg: format!("{}", $msg),
            src: None,
        }));
    };

    ($msg:expr, $src:expr) => {
        return Err(Box::new($crate::error::CmdError {
            msg: format!("{}", $msg),
            src: $src,
        }));
    };
}

#[macro_export]
macro_rules! hopefully {
    ($e:expr, $msg:expr) => {
        $e.map_err(|e| $crate::error::CmdError {
            msg: format!("{}: {}", $msg, e),
            src: Some(Box::new(e)),
        })
    };
}

#[macro_export]
macro_rules! hopefully_ok {
    ($e:expr, $msg:expr) => {
        $e.ok_or_else(|| $crate::error::CmdError {
            msg: format!("{}", $msg),
            src: None,
        })
    };
}
