use anchor_lang::prelude::*;
use anchor_spl::token_interface::{
    Mint as IfMint,
    TokenAccount as IfTokenAccount,
    TransferChecked,
    TokenInterface,
};

use anchor_spl::token::ID as SPL_TOKEN_PROGRAM_ID;
use anchor_spl::token_2022::ID as SPL_TOKEN_2022_PROGRAM_ID;

declare_id!("6xdk8nkjjFqBhe4kxbtwZi7VZsQyCTi6vFk4xFDdfWYB"); // change later

pub const POOL_SEED: &[u8] = b"farm_pool";
pub const AUTH_SEED: &[u8] = b"farm_auth";
pub const USER_POS_SEED: &[u8] = b"user_pos";
pub const POOL_REWARD_SEED: &[u8] = b"pool_reward";
pub const USER_REWARD_SEED: &[u8] = b"user_reward";

pub const SCALE: u128 = 1_000_000_000_000; // 1e12

#[program]
pub mod farm {
    use super::*;

    pub fn init_pool(ctx: Context<InitPool>) -> Result<()> {
        let pool = &mut ctx.accounts.pool;
        pool.admin = ctx.accounts.admin.key();
        pool.lp_mint = ctx.accounts.lp_mint.key();
        pool.lp_vault = ctx.accounts.lp_vault.key();
        pool.total_staked = 0;
        pool.paused = false;
        pool.bump_auth = ctx.bumps.pool_authority;

        // basic checks
        require_keys_eq!(ctx.accounts.lp_vault.owner, ctx.accounts.pool_authority.key(), FarmError::InvalidOwner);
        require_keys_eq!(ctx.accounts.lp_vault.mint, ctx.accounts.lp_mint.key(), FarmError::WrongMint);

        Ok(())
    }

    pub fn add_reward(ctx: Context<AddReward>, emission_rate: u64) -> Result<()> {
        let pr = &mut ctx.accounts.pool_reward;
        pr.pool = ctx.accounts.pool.key();
        pr.reward_mint = ctx.accounts.reward_mint.key();
        pr.reward_vault = ctx.accounts.reward_vault.key();
        pr.emission_rate = emission_rate;
        pr.last_update_ts = Clock::get()?.unix_timestamp as u64;
        pr.acc_reward_per_share = 0;
        pr.enabled = true;

        // checks
        require_keys_eq!(ctx.accounts.reward_vault.owner, ctx.accounts.pool_authority.key(), FarmError::InvalidOwner);
        require_keys_eq!(ctx.accounts.reward_vault.mint, ctx.accounts.reward_mint.key(), FarmError::WrongMint);

        Ok(())
    }

    pub fn fund_reward(ctx: Context<FundReward>, amount: u64) -> Result<()> {
        // transfer reward token from admin -> reward_vault
        let decimals = ctx.accounts.reward_mint.decimals;

        let cpi = CpiContext::new(
            select_token_program(
                &ctx.accounts.reward_mint,
                &ctx.accounts.token_program,
                &ctx.accounts.token_program_2022,
            )?,
            TransferChecked {
                from: ctx.accounts.admin_reward_ata.to_account_info(),
                to: ctx.accounts.reward_vault.to_account_info(),
                authority: ctx.accounts.admin.to_account_info(),
                mint: ctx.accounts.reward_mint.to_account_info(),
            },
        );

        anchor_spl::token_interface::transfer_checked(cpi, amount, decimals)?;
        Ok(())
    }

    pub fn pause_pool(ctx: Context<PausePool>, paused: bool) -> Result<()> {
        require_keys_eq!(ctx.accounts.pool.admin, ctx.accounts.admin.key(), FarmError::Unauthorized);
        ctx.accounts.pool.paused = paused;
        Ok(())
    }

    pub fn set_emission_rate(ctx: Context<SetEmissionRate>, new_rate: u64) -> Result<()> {
        require_keys_eq!(ctx.accounts.pool.admin, ctx.accounts.admin.key(), FarmError::Unauthorized);

        // update before changing rate
        let now = Clock::get()?.unix_timestamp as u64;
        update_pool_reward(
            &mut ctx.accounts.pool_reward,
            ctx.accounts.pool.total_staked,
            now,
        )?;

        ctx.accounts.pool_reward.emission_rate = new_rate;
        Ok(())
    }

    pub fn deposit<'info>(ctx: Context<'_, '_, 'info, 'info, Deposit<'info>>, amount: u64) -> Result<()> {
        require!(!ctx.accounts.pool.paused, FarmError::Paused);

        // Update & claim across all reward mints passed in remaining_accounts
        let now = Clock::get()?.unix_timestamp as u64;

        

        process_rewards_and_claim(
            ctx.accounts.pool.key(),
            ctx.accounts.pool.total_staked,
            ctx.accounts.pool.bump_auth,
            &ctx.accounts.pool_authority,
            ctx.accounts.user_position.key(),
            ctx.accounts.user.key(),
            ctx.accounts.user_position.amount,
            &ctx.accounts.token_program,
            &ctx.accounts.token_program_2022,
            ctx.remaining_accounts,
            now,
        )?;
        // Transfer LP from user -> lp_vault
        let lp_decimals = ctx.accounts.lp_mint.decimals;
        let cpi = CpiContext::new(
            select_token_program(&ctx.accounts.lp_mint, &ctx.accounts.token_program, &ctx.accounts.token_program_2022)?,
            TransferChecked {
                from: ctx.accounts.user_lp_ata.to_account_info(),
                to: ctx.accounts.lp_vault.to_account_info(),
                authority: ctx.accounts.user.to_account_info(),
                mint: ctx.accounts.lp_mint.to_account_info(),
            },
        );
        anchor_spl::token_interface::transfer_checked(cpi, amount, lp_decimals)?;

        // Update staking balances
        let pool = &mut ctx.accounts.pool;
        let up = &mut ctx.accounts.user_position;
        pool.total_staked = pool.total_staked.checked_add(amount).ok_or(FarmError::MathOverflow)?;
        up.amount = up.amount.checked_add(amount).ok_or(FarmError::MathOverflow)?;

        Ok(())
    }

    pub fn withdraw<'info>(ctx: Context<'_, '_, 'info, 'info, Withdraw<'info>>, amount: u64) -> Result<()> {
        require!(!ctx.accounts.pool.paused, FarmError::Paused);

        require!(ctx.accounts.user_position.amount >= amount, FarmError::InsufficientStaked);

        // Update & claim across all reward mints passed in remaining_accounts
        let now = Clock::get()?.unix_timestamp as u64;

        

        process_rewards_and_claim(
            ctx.accounts.pool.key(),
            ctx.accounts.pool.total_staked,
            ctx.accounts.pool.bump_auth,
            &ctx.accounts.pool_authority,
            ctx.accounts.user_position.key(),
            ctx.accounts.user.key(),
            ctx.accounts.user_position.amount,
            &ctx.accounts.token_program,
            &ctx.accounts.token_program_2022,
            ctx.remaining_accounts,
            now,
        )?;
        // Transfer LP from lp_vault -> user
        let lp_decimals = ctx.accounts.lp_mint.decimals;
        let pool_key = ctx.accounts.pool.key();
        let seeds: &[&[u8]] = &[
            AUTH_SEED,
            pool_key.as_ref(),
            &[ctx.accounts.pool.bump_auth],
        ];
        let signer = &[&seeds[..]];

        let cpi = CpiContext::new_with_signer(
            select_token_program(&ctx.accounts.lp_mint, &ctx.accounts.token_program, &ctx.accounts.token_program_2022)?,
            TransferChecked {
                from: ctx.accounts.lp_vault.to_account_info(),
                to: ctx.accounts.user_lp_ata.to_account_info(),
                authority: ctx.accounts.pool_authority.to_account_info(),
                mint: ctx.accounts.lp_mint.to_account_info(),
            },
            signer,
        );
        anchor_spl::token_interface::transfer_checked(cpi, amount, lp_decimals)?;

        // Update staking balances
        let pool = &mut ctx.accounts.pool;
        let up = &mut ctx.accounts.user_position;
        pool.total_staked = pool.total_staked.checked_sub(amount).ok_or(FarmError::MathOverflow)?;
        up.amount = up.amount.checked_sub(amount).ok_or(FarmError::MathOverflow)?;

        Ok(())
    }

    pub fn emergency_withdraw(ctx: Context<EmergencyWithdraw>) -> Result<()> {
        // no rewards: only return LP
        let amount = ctx.accounts.user_position.amount;
        require!(amount > 0, FarmError::InsufficientStaked);

        let lp_decimals = ctx.accounts.lp_mint.decimals;
        let pool_key = ctx.accounts.pool.key();
        let seeds: &[&[u8]] = &[
            AUTH_SEED,
            pool_key.as_ref(),
            &[ctx.accounts.pool.bump_auth],
        ];
        let signer = &[&seeds[..]];

        let cpi = CpiContext::new_with_signer(
            select_token_program(&ctx.accounts.lp_mint, &ctx.accounts.token_program, &ctx.accounts.token_program_2022)?,
            TransferChecked {
                from: ctx.accounts.lp_vault.to_account_info(),
                to: ctx.accounts.user_lp_ata.to_account_info(),
                authority: ctx.accounts.pool_authority.to_account_info(),
                mint: ctx.accounts.lp_mint.to_account_info(),
            },
            signer,
        );
        anchor_spl::token_interface::transfer_checked(cpi, amount, lp_decimals)?;

        // reset
        ctx.accounts.pool.total_staked = ctx.accounts.pool.total_staked.checked_sub(amount).ok_or(FarmError::MathOverflow)?;
        ctx.accounts.user_position.amount = 0;

        Ok(())
    }
}

/* -----------------------------
   Accounts
------------------------------*/

#[derive(Accounts)]
pub struct InitPool<'info> {
    #[account(
        init,
        payer = admin,
        seeds = [POOL_SEED, lp_mint.key().as_ref()],
        bump,
        space = 8 + FarmPool::SIZE
    )]
    pub pool: Account<'info, FarmPool>,

    #[account(
        seeds = [AUTH_SEED, pool.key().as_ref()],
        bump
    )]
    /// CHECK: PDA authority for vaults
    pub pool_authority: UncheckedAccount<'info>,

    pub lp_mint: InterfaceAccount<'info, IfMint>,

    #[account(mut)]
    pub lp_vault: InterfaceAccount<'info, IfTokenAccount>,

    #[account(mut)]
    pub admin: Signer<'info>,

    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct AddReward<'info> {
    #[account(mut)]
    pub pool: Account<'info, FarmPool>,

    #[account(
        seeds = [AUTH_SEED, pool.key().as_ref()],
        bump = pool.bump_auth
    )]
    /// CHECK
    pub pool_authority: UncheckedAccount<'info>,

    #[account(
        init,
        payer = admin,
        seeds = [POOL_REWARD_SEED, pool.key().as_ref(), reward_mint.key().as_ref()],
        bump,
        space = 8 + PoolReward::SIZE
    )]
    pub pool_reward: Account<'info, PoolReward>,

    pub reward_mint: InterfaceAccount<'info, IfMint>,

    #[account(mut)]
    pub reward_vault: InterfaceAccount<'info, IfTokenAccount>,

    #[account(mut)]
    pub admin: Signer<'info>,

    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct FundReward<'info> {
    pub pool: Account<'info, FarmPool>,

    #[account(
        seeds = [POOL_REWARD_SEED, pool.key().as_ref(), reward_mint.key().as_ref()],
        bump
    )]
    pub pool_reward: Account<'info, PoolReward>,

    pub reward_mint: InterfaceAccount<'info, IfMint>,

    #[account(mut)]
    pub admin_reward_ata: InterfaceAccount<'info, IfTokenAccount>,

    #[account(mut)]
    pub reward_vault: InterfaceAccount<'info, IfTokenAccount>,

    #[account(mut)]
    pub admin: Signer<'info>,

    /// CHECK: verified by address constraint
    #[account(address = anchor_spl::token::ID)]
    pub token_program: UncheckedAccount<'info>,

    /// CHECK: verified by address constraint
    #[account(address = anchor_spl::token_2022::ID)]
    pub token_program_2022: UncheckedAccount<'info>,
}

#[derive(Accounts)]
pub struct PausePool<'info> {
    #[account(mut)]
    pub pool: Account<'info, FarmPool>,
    pub admin: Signer<'info>,
}

#[derive(Accounts)]
pub struct SetEmissionRate<'info> {
    #[account(mut)]
    pub pool: Account<'info, FarmPool>,

    #[account(
        mut,
        seeds = [POOL_REWARD_SEED, pool.key().as_ref(), pool_reward.reward_mint.as_ref()],
        bump
    )]
    pub pool_reward: Account<'info, PoolReward>,

    pub admin: Signer<'info>,
}

#[derive(Accounts)]
pub struct Deposit<'info> {
    #[account(mut, seeds = [POOL_SEED, lp_mint.key().as_ref()], bump)]
    pub pool: Account<'info, FarmPool>,

    #[account(
        seeds = [AUTH_SEED, pool.key().as_ref()],
        bump = pool.bump_auth
    )]
    /// CHECK
    pub pool_authority: UncheckedAccount<'info>,

    pub lp_mint: InterfaceAccount<'info, IfMint>,

    #[account(mut)]
    pub lp_vault: InterfaceAccount<'info, IfTokenAccount>,

    #[account(mut)]
    pub user_lp_ata: InterfaceAccount<'info, IfTokenAccount>,

    #[account(
        init_if_needed,
        payer = user,
        seeds = [USER_POS_SEED, pool.key().as_ref(), user.key().as_ref()],
        bump,
        space = 8 + UserPosition::SIZE
    )]
    pub user_position: Account<'info, UserPosition>,

    #[account(mut)]
    pub user: Signer<'info>,

    /// CHECK: verified by address constraint
    #[account(address = anchor_spl::token::ID)]
    pub token_program: UncheckedAccount<'info>,

    /// CHECK: verified by address constraint
    #[account(address = anchor_spl::token_2022::ID)]
    pub token_program_2022: UncheckedAccount<'info>,

    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Withdraw<'info> {
    #[account(mut, seeds = [POOL_SEED, lp_mint.key().as_ref()], bump)]
    pub pool: Account<'info, FarmPool>,

    #[account(
        seeds = [AUTH_SEED, pool.key().as_ref()],
        bump = pool.bump_auth
    )]
    /// CHECK
    pub pool_authority: UncheckedAccount<'info>,

    pub lp_mint: InterfaceAccount<'info, IfMint>,

    #[account(mut)]
    pub lp_vault: InterfaceAccount<'info, IfTokenAccount>,

    #[account(mut)]
    pub user_lp_ata: InterfaceAccount<'info, IfTokenAccount>,

    #[account(mut, seeds = [USER_POS_SEED, pool.key().as_ref(), user.key().as_ref()], bump)]
    pub user_position: Account<'info, UserPosition>,

    #[account(mut)]
    pub user: Signer<'info>,

    /// CHECK: verified by address constraint
    #[account(address = anchor_spl::token::ID)]
    pub token_program: UncheckedAccount<'info>,

    /// CHECK: verified by address constraint
    #[account(address = anchor_spl::token_2022::ID)]
    pub token_program_2022: UncheckedAccount<'info>,
}

#[derive(Accounts)]
pub struct EmergencyWithdraw<'info> {
    #[account(mut, seeds = [POOL_SEED, lp_mint.key().as_ref()], bump)]
    pub pool: Account<'info, FarmPool>,

    #[account(
        seeds = [AUTH_SEED, pool.key().as_ref()],
        bump = pool.bump_auth
    )]
    /// CHECK
    pub pool_authority: UncheckedAccount<'info>,

    pub lp_mint: InterfaceAccount<'info, IfMint>,

    #[account(mut)]
    pub lp_vault: InterfaceAccount<'info, IfTokenAccount>,

    #[account(mut)]
    pub user_lp_ata: InterfaceAccount<'info, IfTokenAccount>,

    #[account(mut, seeds = [USER_POS_SEED, pool.key().as_ref(), user.key().as_ref()], bump)]
    pub user_position: Account<'info, UserPosition>,

    pub user: Signer<'info>,

    /// CHECK: verified by address constraint
    #[account(address = anchor_spl::token::ID)]
    pub token_program: UncheckedAccount<'info>,

    /// CHECK: verified by address constraint
    #[account(address = anchor_spl::token_2022::ID)]
    pub token_program_2022: UncheckedAccount<'info>,
}

/* -----------------------------
   State
------------------------------*/

#[account]
pub struct FarmPool {
    pub admin: Pubkey,
    pub lp_mint: Pubkey,
    pub lp_vault: Pubkey,
    pub total_staked: u64,
    pub paused: bool,
    pub bump_auth: u8,
}

impl FarmPool {
    pub const SIZE: usize =
        32 + // admin
        32 + // lp_mint
        32 + // lp_vault
        8  + // total_staked
        1  + // paused
        1;   // bump_auth
}

#[account]
pub struct PoolReward {
    pub pool: Pubkey,
    pub reward_mint: Pubkey,
    pub reward_vault: Pubkey,
    pub emission_rate: u64,
    pub last_update_ts: u64,
    pub acc_reward_per_share: u128,
    pub enabled: bool,
}

impl PoolReward {
    pub const SIZE: usize =
        32 + // pool
        32 + // reward_mint
        32 + // reward_vault
        8  + // emission_rate
        8  + // last_update_ts
        16 + // acc_reward_per_share
        1;   // enabled
}

#[account]
pub struct UserPosition {
    pub owner: Pubkey,
    pub pool: Pubkey,
    pub amount: u64,
}

impl UserPosition {
    pub const SIZE: usize =
        32 + // owner
        32 + // pool
        8;   // amount
}

#[account]
pub struct UserReward {
    pub user_pos: Pubkey,
    pub reward_mint: Pubkey,
    pub reward_debt: u128,
}

impl UserReward {
    pub const SIZE: usize =
        32 + // user_pos
        32 + // reward_mint
        16;  // reward_debt
}

/* -----------------------------
   Core reward processing
------------------------------*/

fn update_pool_reward(pr: &mut PoolReward, total_staked: u64, now: u64) -> Result<()> {
    if !pr.enabled {
        pr.last_update_ts = now;
        return Ok(());
    }
    let dt = now.saturating_sub(pr.last_update_ts);
    if dt == 0 || total_staked == 0 {
        pr.last_update_ts = now;
        return Ok(());
    }

    let reward: u128 = (dt as u128)
        .checked_mul(pr.emission_rate as u128)
        .ok_or(FarmError::MathOverflow)?;

    pr.acc_reward_per_share = pr.acc_reward_per_share
        .checked_add(
            reward
                .checked_mul(SCALE).ok_or(FarmError::MathOverflow)?
                .checked_div(total_staked as u128).ok_or(FarmError::MathOverflow)?
        )
        .ok_or(FarmError::MathOverflow)?;

    pr.last_update_ts = now;
    Ok(())
}


/// Processes remaining accounts in chunks of 5:
/// [pool_reward, reward_mint, reward_vault, user_reward, user_reward_ata]
fn process_rewards_and_claim<'info>(
    pool_key: Pubkey,
    pool_total_staked: u64,
    pool_bump_auth: u8,
    pool_authority: &UncheckedAccount<'info>,
    user_pos_key: Pubkey,
    user_key: Pubkey,
    user_staked: u64,
    token_program: &UncheckedAccount<'info>,
    token_program_2022: &UncheckedAccount<'info>,
    remaining: &'info [AccountInfo<'info>],
    now: u64,
) -> Result<()> {
    require!(remaining.len() % 5 == 0, FarmError::BadRemainingAccounts);

    let seeds: &[&[u8]] = &[AUTH_SEED, pool_key.as_ref(), &[pool_bump_auth]];
    let signer = &[&seeds[..]];

    // only convert once, INSIDE, tied to 'info
    let pool_authority_ai = pool_authority.to_account_info();
    let token_ai = token_program.to_account_info();
    let token2022_ai = token_program_2022.to_account_info();

    let mut i = 0usize;
    while i < remaining.len() {
        let pr_ai = &remaining[i];
        let mint_ai = &remaining[i + 1];
        let vault_ai = &remaining[i + 2];
        let ur_ai = &remaining[i + 3];
        let user_ata_ai = &remaining[i + 4];

        let mut pr: Account<PoolReward> = Account::try_from(pr_ai)?;
        let mint: InterfaceAccount<IfMint> = InterfaceAccount::try_from(mint_ai)?;
        let vault: InterfaceAccount<IfTokenAccount> = InterfaceAccount::try_from(vault_ai)?;
        let mut ur: Account<UserReward> = Account::try_from(ur_ai)?;
        let user_ata: InterfaceAccount<IfTokenAccount> = InterfaceAccount::try_from(user_ata_ai)?;

        require_keys_eq!(pr.pool, pool_key, FarmError::BadPoolReward);
        require_keys_eq!(ur.user_pos, user_pos_key, FarmError::BadUserReward);

        require_keys_eq!(pr.reward_mint, mint.key(), FarmError::WrongMint);
        require_keys_eq!(pr.reward_vault, vault.key(), FarmError::WrongVault);
        require_keys_eq!(ur.reward_mint, mint.key(), FarmError::WrongMint);

        require_keys_eq!(vault.owner, pool_authority_ai.key(), FarmError::InvalidOwner);
        require_keys_eq!(vault.mint, mint.key(), FarmError::WrongMint);
        require_keys_eq!(user_ata.owner, user_key, FarmError::InvalidOwner);
        require_keys_eq!(user_ata.mint, mint.key(), FarmError::WrongMint);

        update_pool_reward(&mut pr, pool_total_staked, now)?;

        let accrued = (user_staked as u128)
            .checked_mul(pr.acc_reward_per_share)
            .and_then(|v| v.checked_div(SCALE))
            .ok_or(FarmError::MathOverflow)?;

        let pending = accrued.checked_sub(ur.reward_debt).unwrap_or(0);

        if pending > 0 {
            let pending_u64: u64 = pending.try_into().map_err(|_| FarmError::MathOverflow)?;
            let pay = pending_u64.min(vault.amount);

            if pay > 0 {
                let decimals = mint.decimals;

                let program_ai = select_token_program_ai(&mint, &token_ai, &token2022_ai);

                let cpi = CpiContext::new_with_signer(
                    program_ai,
                    TransferChecked {
                        from: vault.to_account_info(),
                        to: user_ata.to_account_info(),
                        authority: pool_authority_ai.clone(),
                        mint: mint.to_account_info(),
                    },
                    signer,
                );

                anchor_spl::token_interface::transfer_checked(cpi, pay, decimals)?;
            }
        }

        ur.reward_debt = accrued;

        pr.exit(&pr_ai.key())?;
        ur.exit(&ur_ai.key())?;

        i += 5;
    }

    Ok(())
}


fn select_token_program_ai<'info>(
    mint: &InterfaceAccount<'info, IfMint>,
    token_program: &AccountInfo<'info>,
    token_program_2022: &AccountInfo<'info>,
) -> AccountInfo<'info> {
    if mint.to_account_info().owner == &anchor_spl::token_2022::ID {
        token_program_2022.clone()
    } else {
        token_program.clone()
    }
}




/* -----------------------------
   Token program selection
------------------------------*/

// fn program_from_mint_owner<'info>(mint: &InterfaceAccount<'info, IfMint>) -> Result<AccountInfo<'info>> {
//     let owner = mint.to_account_info().owner;
//     if *owner == SPL_TOKEN_PROGRAM_ID {
//         Ok(anchor_spl::token::Token::id().into())
//     } else if *owner == SPL_TOKEN_2022_PROGRAM_ID {
//         Ok(anchor_spl::token_2022::Token2022::id().into())
//     } else {
//         Err(FarmError::WrongProgram.into())
//     }
// }

// Used in non-remaining contexts
fn select_token_program<'info>(
    mint: &InterfaceAccount<'info, IfMint>,
    spl_token_program: &UncheckedAccount<'info>,
    spl_token2022_program: &UncheckedAccount<'info>,
) -> Result<AccountInfo<'info>> {
    if mint.to_account_info().owner == &anchor_spl::token_2022::ID {
        Ok(spl_token2022_program.to_account_info())
    } else {
        Ok(spl_token_program.to_account_info())
    }
}

/* -----------------------------
   Errors
------------------------------*/

#[error_code]
pub enum FarmError {
    #[msg("Unauthorized")]
    Unauthorized,
    #[msg("Paused")]
    Paused,
    #[msg("Math overflow")]
    MathOverflow,
    #[msg("Insufficient staked")]
    InsufficientStaked,
    #[msg("Wrong mint")]
    WrongMint,
    #[msg("Wrong vault")]
    WrongVault,
    #[msg("Invalid owner")]
    InvalidOwner,
    #[msg("Bad remaining accounts list")]
    BadRemainingAccounts,
    #[msg("Bad PoolReward")]
    BadPoolReward,
    #[msg("Bad UserReward")]
    BadUserReward,
    #[msg("Wrong token program")]
    WrongProgram,
}
