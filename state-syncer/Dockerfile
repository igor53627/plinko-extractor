# Build stage
FROM rust:1.82-slim-bookworm as builder

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
RUN cargo build --release --bin state-syncer || true

# Now copy the real source code
COPY state-syncer/src state-syncer/src
# Touch main.rs to force rebuild
RUN touch state-syncer/src/main.rs

# Build the actual binary
RUN cargo build --release --bin state-syncer

# Runtime stage
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y ca-certificates && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# Copy binary
COPY --from=builder /app/target/release/state-syncer /usr/local/bin/

# Create data directories
RUN mkdir -p /data /public/deltas /public/snapshots

# Environment defaults
ENV PLINKO_STATE_DB_PATH=/data/database.bin
ENV PLINKO_STATE_ADDRESS_MAPPING_PATH=/data/address-mapping.bin
ENV PLINKO_STATE_PUBLIC_ROOT=/public
ENV PLINKO_STATE_HTTP_PORT=3002
ENV RUST_LOG=info

EXPOSE 3002

CMD ["state-syncer"]
