use clap::Parser;
use std::path::PathBuf;

pub const WORD_SIZE: usize = 32;

pub const SEED_LABEL_REGULAR: &[u8] = b"plinko_regular_subset";
pub const SEED_LABEL_BACKUP: &[u8] = b"plinko_backup_subset";

#[derive(Parser, Debug)]
#[command(author, version, about = "Plinko PIR Hint Generator (Paper-compliant)", long_about = None)]
pub struct Args {
    #[arg(short, long, default_value = "/mnt/plinko/data/database.bin")]
    pub db_path: PathBuf,

    #[arg(short, long, default_value = "128")]
    pub lambda: usize,

    #[arg(short, long)]
    pub backup_hints: Option<usize>,

    #[arg(short, long)]
    pub entries_per_block: Option<usize>,

    #[arg(long, default_value = "false", hide = true)]
    pub allow_truncation: bool,

    #[arg(long)]
    pub seed: Option<String>,

    #[arg(long)]
    pub print_seed: bool,

    #[arg(long)]
    pub constant_time: bool,
}

pub struct RegularHint {
    pub subset_seed: [u8; 32],
    pub parity: [u8; 32],
}

pub struct BackupHint {
    pub subset_seed: [u8; 32],
    pub parity_in: [u8; 32],
    pub parity_out: [u8; 32],
}
