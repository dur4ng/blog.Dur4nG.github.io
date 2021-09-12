---
id: 0
title: "Solana Slp Token program"
subtitle: "I will deconstruct slp token program to undertand how you can create tokens and uses it with all the functionality of the ERC1155 like standard"
date: "2021.09.11"
tags: "solana, slp"
---

# slp program

## Basic Architecture of a smart contract in solana

We must undertand in first place that a smart contract is a system program in the blockchain. Like all programs it need space to locate the program itself and some space for the state. Knowing this we can undertand that a smart contract is a program locate in a blockchain that have a data. In solana the locating of data are accounts. Accounts are space in the blockchain with pairkeys to access it. Accounts in solana has a rent system that you must paid periodly to life in the blockchain. So, we will play with a lot of accounts and the ownership of them to make transactions, locate metadata and so on. In solana smart contract development when we are making transactions we will use all accounts inplicated in that transaction, so we must validate all accounts that we recieve.

> You can check in solana.docs: https://docs.solana.com/developing/programming-model/accounts

Ones we got the basics about how accounts works in solana we can start speaking about the programming model.
You need to undertand that we are creating a system program in a blockchain and a client we will send instructions that the system uses to make transactions.

How does it works, ok it is a complex process but i think is easy to undertand:
- From the client site you will craft instructions that you will serialize and send it to our program in the blockchain
- The program recieve a buch of bytes that will deserialize and try to process it. If it match we some instruction that it has, it will process the instruction modifiying it state.

So in our program we will have an lib, entrypoint, error enums, instructions, processor and a state.

## solana_program crate
solana_program crate is the main library that you will use to develop vanilla smart contract in solana. For that we must be comfortable with this library and undertand what it does and how use it. Let's start:

### account_info
There are two main points that you must undertand from solana_program::account_info and it is that is the struct AccountInfo and function next_account_info:
- AccountInfo has all the data that a account in solana has. 
```rust
pub struct AccountInfo<'a> {
    pub key: &'a Pubkey,
    pub is_signer: bool,
    pub is_writable: bool,
    pub lamports: Rc<RefCell<&'a mut u64>>,
    pub data: Rc<RefCell<&'a mut [u8]>>,
    pub owner: &'a Pubkey,
    pub executable: bool,
    pub rent_epoch: Epoch,
}
```
Fields

key: &'a Pubkey
Public key of the account

is_signer: bool
Was the transaction signed by this account’s public key?

is_writable: bool
Is the account writable?

lamports: Rc<RefCell<&'a mut u64>>
The lamports in the account. Modifiable by programs.

data: Rc<RefCell<&'a mut [u8]>>
The data held in this account. Modifiable by programs.

owner: &'a Pubkey
Program that owns this account

executable: bool
This account’s data contains a loaded program (and is now read-only)

rent_epoch: Epoch
The epoch at which this account will next owe rent

- next_account_info() just iter in and account array.

> You can find more in: https://docs.rs/solana-program/1.7.11/solana_program/account_info/index.html

### instruction
This library defines instructions in solana. What we explained before that in our program we recieve instructions we dont create it. So this library help us to create instructions with testing purposes.
We have two main structs here, AccountMeta and Instruction.

#### AccountMeta
This struct is the metadata that a instruction used.
```rust
pub struct AccountMeta {
    pub pubkey: Pubkey,
    pub is_signer: bool,
    pub is_writable: bool,
}
```
Fields
pubkey: Pubkey
An account’s public key

is_signer: bool
True if an Instruction requires a Transaction signature matching pubkey.

is_writable: bool
True if the pubkey can be loaded as a read-write account.
#### Instruction
This struct defines a instruction
```rust
pub struct Instruction {
    pub program_id: Pubkey,
    pub accounts: Vec<AccountMeta>,
    pub data: Vec<u8>,
}
```
Fields
program_id: Pubkey
Pubkey of the instruction processor that executes this instruction

accounts: Vec<AccountMeta>
Metadata for what accounts should be passed to the instruction processor

data: Vec<u8>
Serialized data passed to the instruction processor

> You can find mnore: https://docs.rs/solana-program/1.7.11/solana_program/instruction/index.html

### entrypoint
From entrypoint we will focus in the entrypoint! macro and the ProgramResult
#### entrypoint!
Is a macro that the defines the entrypoint of our program
#### ProgramResult
You will use it all the time. Is a generic type that can be () or a ProgramError
```rust
pub type ProgramResult = ResultGeneric<(), ProgramError>;
```
> You have all info here: https://docs.rs/solana-program/1.7.11/solana_program/entrypoint/index.html
### pubKey
This crate is extremely important because you are defining the struct that locate addresses in solana blockchain. It implements a buch of functions and traits. This docs are great if you want undertand how you can create, find and log accounts inside solana check this link.

> You have all info here: https://docs.rs/solana-program/1.7.11/solana_program/pubkey/struct.Pubkey.html
### sysvar
This is a big crate but we will use rent crate and Sysvar trait
#### rent
This account contains the current cluster rent

::rent::Rent
```rust
#[repr(C)]
pub struct Rent {
    pub lamports_per_byte_year: u64,
    pub exemption_threshold: f64,
    pub burn_percent: u8,
}
```
Fields
lamports_per_byte_year: u64
Rental rate

exemption_threshold: f64
exemption threshold, in years

burn_percent: u8
> Struct solana_program::rent::Rent https://docs.rs/solana-program/1.7.11/solana_program/rent/struct.Rent.html

#### Sysvar
```rust
pub trait Sysvar: SysvarId + Default + Sized + Serialize + DeserializeOwned {
    fn size_of() -> usize { ... }
    fn from_account_info(
        account_info: &AccountInfo<'_>
    ) -> Result<Self, ProgramError> { ... }
    fn to_account_info(&self, account_info: &mut AccountInfo<'_>) -> Option<()> { ... }
    fn get() -> Result<Self, ProgramError> { ... }
}
```
> Trait solana_program::sysvar::Sysvar https://docs.rs/solana-program/1.7.11/solana_program/sysvar/trait.Sysvar.html


> You have all info here: https://docs.rs/solana-program/1.7.11/solana_program/sysvar/index.html
### program_pack
State transition types. We have three traits:
- IsInitialized check if a program account state is initialized
- Pack Safely and efficietly (de)serialize account state
- Sealed Implementors must have a known size

You must implemented in your own state structs.

### msg
!msg is a macro for logging
### program_option
COption is a type for optional attributes. It can be Some() or None()
### program_error
Is a enum a program error
### decode_error
Is used to build our own error

> Ok we got all basic stuff from the solana_program crate. This will help to defines the basics types a functionalities and make your contract more standard

## lib.rs
Your lib is your personal crate. You must define here all your mods. Is common to set your program id and some helpers.
```rust
#![deny(missing_docs)]
#![cfg_attr(not(test), forbid(unsafe_code))]

//! An ERC20-like Token program for the Solana blockchain

pub mod error;
pub mod instruction;
pub mod native_mint;
pub mod processor;
pub mod state;

#[cfg(not(feature = "no-entrypoint"))]
mod entrypoint;

// Export current sdk types for downstream users building with a different sdk version
pub use solana_program;
use solana_program::{entrypoint::ProgramResult, program_error::ProgramError, pubkey::Pubkey};

/// Convert the UI representation of a token amount (using the decimals field defined in its mint)
/// to the raw amount
pub fn ui_amount_to_amount(ui_amount: f64, decimals: u8) -> u64 {
    (ui_amount * 10_usize.pow(decimals as u32) as f64) as u64
}

/// Convert a raw amount to its UI representation (using the decimals field defined in its mint)
pub fn amount_to_ui_amount(amount: u64, decimals: u8) -> f64 {
    amount as f64 / 10_usize.pow(decimals as u32) as f64
}

solana_program::declare_id!("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA");

/// Checks that the supplied program ID is the correct one for SPL-token
pub fn check_program_account(spl_token_program_id: &Pubkey) -> ProgramResult {
    if spl_token_program_id != &id() {
        return Err(ProgramError::IncorrectProgramId);
    }
    Ok(())
}
```
## entrypoint.rs
The entrypoint cant be other think that the entrypoint of our program. You just need you to define a function that call the processor and put it in a entrypoint! macro. What you are doing is setting the entrypoint of your program and pass some data to your processor and this one will deserialze the instruction and execute it.
```rust
//! Program entrypoint

use crate::{error::TokenError, processor::Processor};
use solana_program::{
    account_info::AccountInfo,
    entrypoint,
    entrypoint::ProgramResult,
    program_error::PrintProgramError,
    pubkey::Pubkey,
};

entrypoint!(process_instruction);
fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    if let Err(error) = Processor::process(program_id, accounts, instruction_data) {
        // catch the error so we can print it
        error.print::<TokenError>();
        return Err(error);
    }
    Ok(())
}
```
## error.rs

For implementing error for our smart contract we can use the ProgramError enum of the solana_program crate. But we can create our custom errors.
For our error we just need to create an Error enum that implements some traits. To implements so basic traits in rust you can use #[derive()] attribute in the top of your enum or struct. For our enum we will implement Clone, Debug, Eq, Error, FromPrimitive, ParitalEq. 
- Clone make your erros clonables.
- Debug give you format for log your errors.
- Eq makes your enum comparable.
- PartialEq like Eq but less restrictive
- Error ?
- FromPrimitive A generic trait for converting a number to a value

For each error inside the enum you mark it as an error using #[error("custom name")] attribute

Now we must impl our custom errors into the standar enum of solana_program. We impl DecodeError to our custom enum and then implement our custom enum for the solana_program::ProgramError

```rust
impl From<TokenError> for ProgramError {
    fn from(e: TokenError) -> Self {
        ProgramError::Custom(e as u32)
    }
}
impl<T> DecodeError<T> for TokenError {
    fn type_of() -> &'static str {
        "TokenError"
    }
}
```
## state.rs
The state of our program is really important. Its were the data for our smart contracts is. Main main idea is that we will create our own state structs and we will impl some traits to apply some basic funcionality like (de)serialize.
I will show you Mint state struct from slp token program as example:
```rust
//! State transition types

use crate::instruction::MAX_SIGNERS;
use arrayref::{array_mut_ref, array_ref, array_refs, mut_array_refs};
use num_enum::TryFromPrimitive;
use solana_program::{
    program_error::ProgramError,
    program_option::COption,
    program_pack::{IsInitialized, Pack, Sealed},
    pubkey::Pubkey,
};

/// Mint data.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Mint { 1
    /// Optional authority used to mint new tokens. The mint authority may only be provided during
    /// mint creation. If no mint authority is present then the mint has a fixed supply and no
    /// further tokens may be minted.
    pub mint_authority: COption<Pubkey>,
    /// Total supply of tokens.
    pub supply: u64,
    /// Number of base 10 digits to the right of the decimal place.
    pub decimals: u8,
    /// Is `true` if this structure has been initialized
    pub is_initialized: bool,
    /// Optional authority to freeze token accounts.
    pub freeze_authority: COption<Pubkey>,
}
impl Sealed for Mint {} 2
impl IsInitialized for Mint { 3
    fn is_initialized(&self) -> bool {
        self.is_initialized
    }
}
impl Pack for Mint { 4
    const LEN: usize = 82;
    fn unpack_from_slice(src: &[u8]) -> Result<Self, ProgramError> { 5
        let src = array_ref![src, 0, 82]; 6
        let (mint_authority, supply, decimals, is_initialized, freeze_authority) =
            array_refs![src, 36, 8, 1, 1, 36];
        let mint_authority = unpack_coption_key(mint_authority)?;
        let supply = u64::from_le_bytes(*supply);
        let decimals = decimals[0];
        let is_initialized = match is_initialized {
            [0] => false,
            [1] => true,
            _ => return Err(ProgramError::InvalidAccountData),
        };
        let freeze_authority = unpack_coption_key(freeze_authority)?;
        Ok(Mint {
            mint_authority,
            supply,
            decimals,
            is_initialized,
            freeze_authority,
        })
    }
    fn pack_into_slice(&self, dst: &mut [u8]) { 7
        let dst = array_mut_ref![dst, 0, 82]; 8
        let (
            mint_authority_dst,
            supply_dst,
            decimals_dst,
            is_initialized_dst,
            freeze_authority_dst,
        ) = mut_array_refs![dst, 36, 8, 1, 1, 36]; 8
        let &Mint { 9
            ref mint_authority,
            supply,
            decimals,
            is_initialized,
            ref freeze_authority,
        } = self;
        pack_coption_key(mint_authority, mint_authority_dst);
        *supply_dst = supply.to_le_bytes();
        decimals_dst[0] = decimals;
        is_initialized_dst[0] = is_initialized as u8;
        pack_coption_key(freeze_authority, freeze_authority_dst);
    }
}
```
1 For our Mint we need a mint_authority, sypply, decimals, is_initialized and a freeze_authority all explained.
2 Implementation of Sealed for Mint.
3 IsInitialized is a getter of is_initialized.
4 Is the implementation of (de)serializing for our state
5 In unpack_from_slice we recieve a and array of u8 and the result is a Mint State. 
6 You can use array_refs to generate a series of array references to an input array reference. The idea is if you want to break an array into a series of contiguous and non-overlapping arrays. array_refs is a bit funny in that it insists on slicing up the entire array. This is intentional, as I find it handy to make me ensure that my sub-arrays add up to the entire array. This macro will never panic, since the sizes are all checked at compile time. So we use array_refs! macro to extract the data we want from the input and creating our local variables for them, we must unpack the non primitive types and return our Mint State.
7 In pack_into_slice we recieve a Mint State and a dst(dynamic sized types) that it will be the data. Dst are specials types with a size that is known only at run-time, like a trait object or a slice. 8 First we will use array_mut_ref! and mut_array_refs! macros like before to extract the data from dst variable. 9 Then we set the data structure Mint, pack the mints authoritys, get the memory representation of our supply, set our decimals, set our is_initialized as a u8 and pack the freezes authorities. When you pack you changes the state.

Note that unlike array_ref!, array_refs requires that the first argument be an array reference. The following arguments are the lengths of each subarray you wish a reference to. The total of these arguments must equal the size of the array itself.
## instruction.rs
In the instruction file is the enums of the funcionality of your program and must implement (de)serialization. You must think in you will not have only one instruction inside a enum Instruction type, you will possible have tens of instructions. So you must a system for identify what instruction is when you deserialize it. The standar is putting a number in the buffer. When you deseriale your instruction the firsts thing that you will do is extract that number to identify what instrcution is.
Usually you can create functions in this file that craft instruction for testing purposes.

```rust
#[repr(C)]
#[derive(Clone, Debug, PartialEq)]
pub enum TokenInstruction {
    /// Initializes a new mint and optionally deposits all the newly minted
    /// tokens in an account.
    ///
    /// The `InitializeMint` instruction requires no signers and MUST be
    /// included within the same Transaction as the system program's
    /// `CreateAccount` instruction that creates the account being initialized.
    /// Otherwise another party can acquire ownership of the uninitialized
    /// account.
    ///
    /// Accounts expected by this instruction:
    ///
    ///   0. `[writable]` The mint to initialize.
    ///   1. `[]` Rent sysvar
    ///
    InitializeMint {
        /// Number of base 10 digits to the right of the decimal place.
        decimals: u8,
        /// The authority/multisignature to mint tokens.
        mint_authority: Pubkey,
        /// The freeze authority/multisignature of the mint.
        freeze_authority: COption<Pubkey>,
    }
}
impl TokenInstruction {
    /// Unpacks a byte buffer into a [TokenInstruction](enum.TokenInstruction.html).
    pub fn unpack(input: &[u8]) -> Result<Self, ProgramError> {
        use TokenError::InvalidInstruction;

        let (&tag, rest) = input.split_first().ok_or(InvalidInstruction)?;
        Ok(match tag {
            0 => {
                let (&decimals, rest) = rest.split_first().ok_or(InvalidInstruction)?;
                let (mint_authority, rest) = Self::unpack_pubkey(rest)?;
                let (freeze_authority, _rest) = Self::unpack_pubkey_option(rest)?;
                Self::InitializeMint {
                    mint_authority,
                    freeze_authority,
                    decimals,
                }
            }
            _ => return Err(TokenError::InvalidInstruction.into()),
        })
    }

    /// Packs a [TokenInstruction](enum.TokenInstruction.html) into a byte buffer.
    pub fn pack(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(size_of::<Self>());
        match self {
            &Self::InitializeMint {
                ref mint_authority,
                ref freeze_authority,
                decimals,
            } => {
                buf.push(0);
                buf.push(decimals);
                buf.extend_from_slice(mint_authority.as_ref());
                Self::pack_pubkey_option(freeze_authority, &mut buf);
            }
        };
        buf
    }

    fn unpack_pubkey(input: &[u8]) -> Result<(Pubkey, &[u8]), ProgramError> {
        if input.len() >= 32 {
            let (key, rest) = input.split_at(32);
            let pk = Pubkey::new(key);
            Ok((pk, rest))
        } else {
            Err(TokenError::InvalidInstruction.into())
        }
    }

    fn unpack_pubkey_option(input: &[u8]) -> Result<(COption<Pubkey>, &[u8]), ProgramError> {
        match input.split_first() {
            Option::Some((&0, rest)) => Ok((COption::None, rest)),
            Option::Some((&1, rest)) if rest.len() >= 32 => {
                let (key, rest) = rest.split_at(32);
                let pk = Pubkey::new(key);
                Ok((COption::Some(pk), rest))
            }
            _ => Err(TokenError::InvalidInstruction.into()),
        }
    }

    fn pack_pubkey_option(value: &COption<Pubkey>, buf: &mut Vec<u8>) {
        match *value {
            COption::Some(ref key) => {
                buf.push(1);
                buf.extend_from_slice(&key.to_bytes());
            }
            COption::None => buf.push(0),
        }
    }
}

> Is very import that explain what each instruction and variables does. Its can be extremely helpfull for other devs.
```
## processor.rs
Here is were the magic happens. In this file you will define a Processor struct and you will implement it all instructions processor functions. The standar is using a entry function called process and inside deserialize the inputs and match the processor function it needs.
```rust
pub struct Processor {}
impl Processor {

/// Processes an [Instruction](enum.Instruction.html).
    pub fn process(program_id: &Pubkey, accounts: &[AccountInfo], input: &[u8]) -> ProgramResult {
        let instruction = TokenInstruction::unpack(input)?;

        match instruction {
            TokenInstruction::InitializeMint {
                decimals,
                mint_authority,
                freeze_authority,
            } => {
                msg!("Instruction: InitializeMint");
                Self::process_initialize_mint(accounts, decimals, mint_authority, freeze_authority)
            }
        }
    }

    fn _process_initialize_mint(
        accounts: &[AccountInfo],
        decimals: u8,
        mint_authority: Pubkey,
        freeze_authority: COption<Pubkey>,
        rent_sysvar_account: bool,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let mint_info = next_account_info(account_info_iter)?;
        let mint_data_len = mint_info.data_len();
        let rent = if rent_sysvar_account {
            Rent::from_account_info(next_account_info(account_info_iter)?)?
        } else {
            Rent::get()?
        };

        let mut mint = Mint::unpack_unchecked(&mint_info.data.borrow())?;
        if mint.is_initialized {
            return Err(TokenError::AlreadyInUse.into());
        }

        if !rent.is_exempt(mint_info.lamports(), mint_data_len) {
            return Err(TokenError::NotRentExempt.into());
        }

        mint.mint_authority = COption::Some(mint_authority);
        mint.decimals = decimals;
        mint.is_initialized = true;
        mint.freeze_authority = freeze_authority;

        Mint::pack(mint, &mut mint_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes an [InitializeMint](enum.TokenInstruction.html) instruction.
    pub fn process_initialize_mint(
        accounts: &[AccountInfo],
        decimals: u8,
        mint_authority: Pubkey,
        freeze_authority: COption<Pubkey>,
    ) -> ProgramResult {
        Self::_process_initialize_mint(accounts, decimals, mint_authority, freeze_authority, true)
    }
}
```