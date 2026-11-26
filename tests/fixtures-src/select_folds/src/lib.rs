#![no_std]
use soroban_sdk::{contract, contracterror, contractimpl, panic_with_error, symbol_short, Env};

#[contract]
pub struct Contract;

#[contracterror]
#[derive(Debug, PartialEq)]
pub enum Error {
    NotPositive = 1,
}

#[contractimpl]
impl Contract {
    /// `amount <= 0` on an `i128` is a `select` over its two limbs.
    pub fn deposit(env: Env, amount: i128) {
        if amount <= 0 {
            panic_with_error!(&env, Error::NotPositive);
        }
        env.storage().instance().set(&symbol_short!("amount"), &amount);
    }

    /// `min` picks each limb with a `select` on one two-limb compare.
    pub fn smaller(a: i128, b: i128) -> i128 {
        a.min(b)
    }
}
