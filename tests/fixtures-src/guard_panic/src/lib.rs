#![no_std]
use soroban_sdk::{contract, contracterror, contractimpl, panic_with_error, Env};

#[contract]
pub struct Contract;

#[contracterror]
#[derive(Debug, PartialEq)]
pub enum Error {
    BadDecimals = 1,
}

#[contractimpl]
impl Contract {
    /// The guarded value is also the returned one: the success path proves
    /// `decimals == 7`, so the tail folds to `7` — but the guard itself must
    /// survive, or `check(8)` returns 7 instead of failing.
    pub fn check(env: Env, decimals: u32) -> u32 {
        if decimals != 7 {
            panic_with_error!(&env, Error::BadDecimals);
        }
        decimals
    }

    /// The guarded value is NOT the returned one, so no folding can stand in
    /// for the guard.
    pub fn check_other(env: Env, decimals: u32, amount: u32) -> u32 {
        if decimals != 7 {
            panic_with_error!(&env, Error::BadDecimals);
        }
        amount
    }
}
