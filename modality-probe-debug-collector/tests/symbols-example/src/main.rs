//! Blinks an LED

//#![deny(unsafe_code)]
#![deny(warnings)]
#![no_main]
#![no_std]

extern crate panic_halt;
#[cfg(target_endian = "little")]
use cortex_m_rt::entry;

#[no_mangle]
static mut v1: u32 = 1;
#[no_mangle]
static mut v2: u32 = 1;
#[no_mangle]
static mut v3: u32 = 1;

#[cfg(target_endian = "little")]
#[entry]
fn main() -> ! {
    loop {
        unsafe {
            v1+=1;
            v2+=1;
            v3+=1;
        }
    }
}
