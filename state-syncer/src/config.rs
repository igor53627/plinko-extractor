use std::path::PathBuf;
use std::time::Duration;
use clap::Parser;

#[derive(Parser, Debug, Clone)]
pub struct Config {
    /// Canonical database file to mutate in place
    #[arg(long, env = "PLINKO_STATE_DB_PATH", default_value = "/data/database.bin")]
    pub database_path: PathBuf,

    /// Input mapping file to copy into the public artifacts volume
    #[arg(long, env = "PLINKO_STATE_ADDRESS_MAPPING_PATH", default_value = "/data/account-mapping.bin")]
    pub address_mapping_path: PathBuf,

    /// Root directory for artifacts served by the CDN mock
    #[arg(long, env = "PLINKO_STATE_PUBLIC_ROOT", default_value = "/public")]
    pub public_root: PathBuf,

    /// Directory for per-block delta files
    #[arg(long, env = "PLINKO_STATE_DELTA_DIR", default_value = "/public/deltas")]
    pub delta_dir: PathBuf,

    /// Port for the embedded health/metrics server
    #[arg(long, env = "PLINKO_STATE_HTTP_PORT", default_value = "3002")]
    pub http_port: u16,

    /// HTTP API for the bundled ipfs/kubo daemon
    #[arg(long, env = "PLINKO_STATE_IPFS_API")]
    pub ipfs_api: Option<String>,

    /// Gateway base advertised inside manifest.json
    #[arg(long, env = "PLINKO_STATE_IPFS_GATEWAY", default_value = "http://localhost:8080/ipfs")]
    pub ipfs_gateway: String,

    /// Ethereum RPC/Hypersync endpoint
    #[arg(long, env = "PLINKO_STATE_RPC_URL", default_value = "http://eth-mock:8545")]
    pub rpc_url: String,

    /// Optional bearer token for Hypersync
    #[arg(long, env = "PLINKO_STATE_RPC_TOKEN")]
    pub rpc_token: Option<String>,

    /// Block height that matches the seeded snapshot
    #[arg(long, env = "PLINKO_STATE_START_BLOCK")]
    pub start_block: Option<u64>,

    /// Use deterministic fake updates instead of hitting RPC
    #[arg(long, env = "PLINKO_STATE_SIMULATED", default_value = "true")]
    pub simulated: bool,

    /// Delay between RPC polls when the chain head is behind (ms)
    #[arg(long, env = "PLINKO_STATE_POLL_INTERVAL", default_value = "5000")]
    pub poll_interval_ms: u64,

    /// Publish a snapshot every N processed blocks (0 disables)
    #[arg(long, env = "PLINKO_STATE_SNAPSHOT_EVERY", default_value = "0")]
    pub snapshot_every: u64,

    /// Number of concurrent block fetches
    #[arg(long, env = "PLINKO_STATE_CONCURRENCY", default_value = "10")]
    pub concurrency: usize,
}

impl Config {
    pub fn snapshots_root(&self) -> PathBuf {
        self.public_root.join("snapshots")
    }

    pub fn public_address_mapping_path(&self) -> PathBuf {
        self.public_root.join("account-mapping.bin")
    }
    
    pub fn poll_interval(&self) -> Duration {
        Duration::from_millis(self.poll_interval_ms)
    }
}
