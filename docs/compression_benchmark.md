# Plinko Database Compression Benchmark

**Date:** November 25, 2025  
**Source Data:** Ethereum State Database (Flat Binary)  
**Original Size:** 82 GB (87,296,475,320 bytes)

We compared **Brotli** (Google) and **Zstandard** (Facebook) to determine the optimal compression algorithm for distributing Plinko PIR database snapshots.

## Results

| Algorithm | Settings | Compressed Size | Compression Ratio | Time Taken | Speed |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Brotli** | `-q 6` (Default) | **9.6 GB** | **8.5x** | 2,250s (37m) | ~37 MB/s |
| **Zstd** | `-3` (Default) | **11.0 GB** | **7.5x** | **351s (6m)** | **~239 MB/s** |

> **Note:** Testing `Brotli -q 11` (Max) yielded diminishing returns (worse ratio than `-q 6` on small samples) and was prohibitively slow (~4.5 days est. for full DB).

## Analysis

### 1. Storage & Bandwidth
**Winner: Brotli**
Brotli saves an additional **1.4 GB** (12.7%) compared to Zstd. For a file downloaded by potentially thousands of light clients, this bandwidth saving is significant.

### 2. Speed
**Winner: Zstd**
Zstandard is **6.4x faster** at compression. If snapshots needed to be generated in real-time or every few minutes, Zstd would be the only viable option. However, for daily or weekly snapshots, the 37-minute generation time for Brotli is acceptable.

### 3. Browser Compatibility
**Winner: Brotli**
Brotli (`br`) is natively supported by all modern browsers for `Content-Encoding`, allowing for transparent decompression during download. Zstd (`zstd`) support is growing but less universal for HTTP content encoding.

## Recommendation

We recommend using **Brotli (-q 6)** for distributing the static `database.bin` snapshots.

*   **Command:** `brotli -q 6 -k -f database.bin`
*   **Extension:** `.bin.br`
