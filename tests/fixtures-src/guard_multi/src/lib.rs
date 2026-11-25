#![no_std]
use soroban_sdk::{
    contract, contracterror, contractimpl, panic_with_error, symbol_short, Env, String,
};

#[contract]
pub struct Contract;

#[contracterror]
#[derive(Debug, PartialEq)]
pub enum Error {
    BadName = 1,
    BadDecimals = 2,
}

#[contractimpl]
impl Contract {
    pub fn init(env: Env, name: String, decimals: u32) {
        if name.len() == 0 {
            panic_with_error!(&env, Error::BadName);
        }
        if decimals != 7 {
            panic_with_error!(&env, Error::BadDecimals);
        }
        env.storage().instance().set(&symbol_short!("dec"), &decimals);
    }
}
