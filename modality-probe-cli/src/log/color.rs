use std::sync::RwLock;

use colored::Colorize;
use colorous::Color;

use lazy_static::lazy_static;

lazy_static! {
    pub(crate) static ref COLORIZE: RwLock<bool> = RwLock::new(true);
}

const PROBE_SET: [Color; 12] = colorous::SET3;

pub fn colorize_probe(idx: usize, content: &str) -> String {
    if COLORIZE.read().map(|b| *b).unwrap_or(false) {
        let c = PROBE_SET[idx % PROBE_SET.len()];
        content.truecolor(c.r, c.g, c.b).to_string()
    } else {
        content.to_string()
    }
}

pub fn colorize_info(key: &str, val: &str) -> String {
    if key.is_empty() {
        return String::new();
    }
    if COLORIZE.read().map(|b| *b).unwrap_or(false) {
        format!("{} {}", format!("{}:", key).white(), val.yellow())
    } else {
        format!("{} {}", format!("{}:", key), val)
    }
}

pub fn colorize_merge(from: &str, from_idx: usize, to: &str, to_idx: usize) -> String {
    if COLORIZE.read().map(|b| *b).unwrap_or(false) {
        let from_color = PROBE_SET[from_idx % PROBE_SET.len()];
        let to_color = PROBE_SET[to_idx % PROBE_SET.len()];
        format!(
            "{} merged a snapshot from {}",
            to.truecolor(to_color.r, to_color.g, to_color.b),
            from.truecolor(from_color.r, from_color.g, from_color.b)
        )
    } else {
        format!("{} merged a snapshot from {}", to, from,)
    }
}

pub fn colorize_coord(coord: &str) -> String {
    if COLORIZE.read().map(|b| *b).unwrap_or(false) {
        format!("{}{}{}", "(".white(), coord.yellow(), ")".white())
    } else {
        format!("({})", coord)
    }
}

pub fn white(content: &str) -> String {
    if COLORIZE.read().map(|b| *b).unwrap_or(false) {
        content.white().to_string()
    } else {
        content.to_string()
    }
}

#[cfg(test)]
mod test {
    use proptest::prelude::*;

    use super::*;

    proptest! {
        #[test]
        fn colorize_probe_doesnt_panic(idx in proptest::num::usize::ANY) {
            colorize_probe(idx, "");
        }
    }
}
