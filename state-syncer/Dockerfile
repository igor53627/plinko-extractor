# Build stage
FROM rust:1.82-slim-bookworm as builder
RUN apt-get update && apt-get install -y libssl-dev pkg-config
RUN rustup toolchain install nightly
RUN rustup default nightly

WORKDIR /app

# Copy workspace definition
COPY Cargo.toml Cargo.lock ./

# Create dummy crates to build dependencies first (caching layer)
RUN mkdir -p src && \
    echo "fn main() {}" > src/main.rs && \
    mkdir -p state-syncer/src && \
    echo "fn main() {}" > state-syncer/src/main.rs && \
    touch state-syncer/Cargo.toml

# Copy the actual Cargo.toml files
COPY state-syncer/Cargo.toml state-syncer/
# (If plinko-extractor is part of workspace, copy its toml too, but we focus on state-syncer)

# Build dependencies
RUN cargo build --release -p state-syncer --jobs 2 || true

# Now copy the real source code
COPY state-syncer/src state-syncer/src
# Touch main.rs to force rebuild
RUN touch state-syncer/src/main.rs

# Build the actual binary
RUN cargo build --release -p state-syncer --jobs 2
RUN cargo build --release --bin bench_hints -p state-syncer

# Runtime stage
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y ca-certificates && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# Copy binary
COPY --from=builder /app/target/release/state-syncer /usr/local/bin/
COPY --from=builder /app/target/release/bench_hints /usr/local/bin/

# Create data directories
RUN mkdir -p /data /public/deltas /public/snapshots

# Environment defaults
ENV PLINKO_STATE_DB_PATH=/data/database.bin
ENV PLINKO_STATE_ADDRESS_MAPPING_PATH=/data/account-mapping.bin
ENV PLINKO_STATE_PUBLIC_ROOT=/public
ENV PLINKO_STATE_HTTP_PORT=3002
ENV RUST_LOG=info

EXPOSE 3002

CMD ["state-syncer"]
