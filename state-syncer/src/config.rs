use clap::Parser;
use std::path::PathBuf;
use std::time::Duration;

#[derive(Parser, Debug, Clone)]
pub struct Config {
    /// Canonical database file to mutate in place
    #[arg(
        long,
        env = "PLINKO_STATE_DB_PATH",
        default_value = "/data/database.bin"
    )]
    pub database_path: PathBuf,

    /// Input mapping file to copy into the public artifacts volume
    #[arg(
        long,
        env = "PLINKO_STATE_ADDRESS_MAPPING_PATH",
        default_value = "/data/account-mapping.bin"
    )]
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
    #[arg(
        long,
        env = "PLINKO_STATE_IPFS_GATEWAY",
        default_value = "http://localhost:8080/ipfs"
    )]
    pub ipfs_gateway: String,

    /// Ethereum RPC/Hypersync endpoint
    #[arg(
        long,
        env = "PLINKO_STATE_RPC_URL",
        default_value = "http://eth-mock:8545"
    )]
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

    /// Returns the path to the public account mapping file inside `public_root`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::PathBuf;
    ///
    /// struct Tmp { public_root: PathBuf }
    /// impl Tmp {
    ///     fn public_address_mapping_path(&self) -> PathBuf {
    ///         self.public_root.join("account-mapping.bin")
    ///     }
    /// }
    ///
    /// let cfg = Tmp { public_root: PathBuf::from("/public") };
    /// assert_eq!(
    ///     cfg.public_address_mapping_path(),
    ///     PathBuf::from("/public/account-mapping.bin")
    /// );
    /// ```
    pub fn public_address_mapping_path(&self) -> PathBuf {
        self.public_root.join("account-mapping.bin")
    }

    /// Return the configured poll interval as a `Duration`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use std::path::PathBuf;
    ///
    /// let cfg = Config {
    ///     database_path: PathBuf::from("/data/database.bin"),
    ///     address_mapping_path: PathBuf::from("/data/account-mapping.bin"),
    ///     public_root: PathBuf::from("/public"),
    ///     delta_dir: PathBuf::from("/public/deltas"),
    ///     http_port: 3002,
    ///     ipfs_api: None,
    ///     ipfs_gateway: "http://localhost:8080/ipfs".to_string(),
    ///     rpc_url: "http://eth-mock:8545".to_string(),
    ///     rpc_token: None,
    ///     start_block: None,
    ///     simulated: true,
    ///     poll_interval_ms: 1500,
    ///     snapshot_every: 0,
    ///     concurrency: 10,
    /// };
    ///
    /// assert_eq!(cfg.poll_interval(), Duration::from_millis(1500));
    /// ```
    pub fn poll_interval(&self) -> Duration {
        Duration::from_millis(self.poll_interval_ms)
    }
}