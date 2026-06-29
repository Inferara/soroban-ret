#![no_std]
use soroban_sdk::{contract, contracterror, contractimpl};

#[contract]
pub struct Contract;

#[contracterror]
#[derive(Debug, PartialEq)]
pub enum Error {
    Underflow = 1,
}

#[contracterror]
#[derive(Debug, PartialEq)]
pub enum MyError {
    Underflow = 1,
}

#[contractimpl]
impl Contract {
    pub fn safe_sub(a: u64, b: u64) -> Result<u64, Error> {
        a.checked_sub(b).ok_or(Error::Underflow)
    }
    pub fn safe_sub_two(a: u64, b: u64) -> Result<u64, MyError> {
        a.checked_sub(b).ok_or(MyError::Underflow)
    }
}
