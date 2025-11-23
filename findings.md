# Plinko Extractor: State Size & Performance Findings

This document provides an extrapolation of data sizes for the full Ethereum state (as of late 2025) and estimates the client-side storage requirements for the Plinko PIR protocol.

## 1. Ethereum State Extrapolation (2025)

Based on direct queries from the **Reth** node (`v1.8.2`) on `reth-onion-dev`, we have the following exact counts for the Ethereum Mainnet state (as of current block height):

- **Total Unique Accounts ($N_{acc}$)**: **328,138,215** (Measured)
- **Total Storage Slots ($N_{sto}$)**: **~1,150,000,000** (Estimated, scan ongoing)

### Processed Artifact Sizes

The extractor produces a flat, padded database to ensure O(1) access and alignment.

#### A. `database.bin` (The Raw Data)
*   **Accounts**: occupy 4 words (128 bytes) each.
    *   $328.1M \times 128 \text{ bytes} \approx 42.0 \text{ GB}$
*   **Storage Slots**: occupy 1 word (32 bytes) each.
    *   $1.15B \times 32 \text{ bytes} \approx 36.8 \text{ GB}$
*   **Total Database Size**: **~78.8 GB**

#### B. Mappings (The Index)
*   **Account Mapping**: $328.1M \times (20 \text{ addr} + 4 \text{ idx}) \approx 7.9 \text{ GB}$
*   **Storage Mapping**: $1.15B \times (20 \text{ addr} + 32 \text{ key} + 4 \text{ idx}) \approx 64.4 \text{ GB}$
*   **Total Mapping Size**: **~72.3 GB**

> **Note**: The mapping allows the server to locate data. The PIR client **does not** need the mappings; it only needs the `database.bin` stream to generate hints.

---

## 2. Plinko PIR Client Storage

The Plinko protocol allows a client to query the database privately by storing a small set of "hints" (parities) instead of the full data.

### Parameters
*   **Total DB Entries ($N$)**:
    *   Accounts contribute $328.1M \times 4 = 1.31B$ entries.
    *   Storage contributes $1.15B$ entries.
    *   $N \approx 2.46 \text{ Billion entries}$.
*   **Square Root ($\sqrt{N}$)**: $\approx 49,600$.

### Hint Size Estimation
According to the Plinko tutorial:
> "The client generates roughly $128 * \sqrt{N}$ **hints**... and store data equal to roughly $64 * \sqrt{N}$ cells"

Assuming we need to retrieve full 32-byte words (balances/storage), each "cell" in the hint is 32 bytes (256 bits).

*   **Primary Hint Count**: $128 \times 49,600 \approx 6.35 \text{ million hints}$.
*   **Storage Requirement**:
    *   $6.35M \text{ hints} \times 32 \text{ bytes} \approx 203 \text{ MB}$.

### Backup Hints
For each query we intend to make, we need a backup hint.
*   **Size per Backup Hint**: $\sqrt{N}$ cells.
*   $49,600 \times 32 \text{ bytes} \approx 1.6 \text{ MB}$ per query.

---

## 3. Optimizations & "Concrete Efficiency"

Vitalik's "Concrete Efficiency" (and the Plinko design) relies on treating the database as a square matrix to optimize bandwidth and storage.

### Optimization 1: Client Storage Reduction
*   **Naive Light Client**: Stores headers only, requests Merkle proofs. (High bandwidth per query, no privacy).
*   **Full Node**: Stores ~100GB+ state.
*   **Plinko Client**: Stores **~203 MB** of hints.
    *   **Reduction**: ~99.8% reduction compared to full state.
    *   **Privacy**: Information-theoretic (IT-PIR) for reads.

### Optimization 2: Update Efficiency
The tutorial mentions:
> "There is also an easy way for the client to update hints if the data set changes."

Since hints are linear combinations (XOR sums), updates are efficient. When a block changes $k$ accounts:
1.  Client receives the storage diff (e.g., 300 changes per block).
2.  Client updates relevant hints in $O(1)$ time per change.
3.  **Cost**: Negligible computation compared to re-downloading.

### Optimization 3: Hybrid / "Partially Stateless" (Vitalik's Vision)
If we apply the "Concrete Efficiency" idea of **partially stateless nodes**:
*   We can split the state (e.g., by address prefix).
*   A node/client only maintains hints for the "slice" of the state they care about (e.g., 1/16th of the state).
*   **Result**: Client storage drops from ~203 MB to **~12.7 MB**.

## Conclusion

| Metric | Raw Ethereum State | Plinko Optimized (Client) |
| :--- | :--- | :--- |
| **Data Volume** | ~151 GB (DB + Maps) | **~203 MB** (Hints) |
| **Privacy** | None (Public Read) | **Private** (PIR) |
| **Query Cost** | Local Read (Fast) | 1 Round Trip + XOR |
| **Setup Cost** | Download 151 GB | Stream 79 GB (Once) |

For a light client wallet (like Rabby), storing **~200 MB** of static hints to gain complete read privacy for the entire Ethereum state is a highly practical trade-off.
