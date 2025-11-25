# Plinko Delta File Format

The `state-syncer` service produces per-block delta files (e.g., `delta-23237685.bin`) that allow PIR clients to update their local hints without re-downloading the database.

## File Structure

The file is a binary stream encoded in Little Endian (LE).

| Field | Type | Size (Bytes) | Description |
|-------|------|--------------|-------------|
| **Header** | | **16** | |
| Count | `u64` | 8 | Number of delta records in this file. |
| EntryLength | `u64` | 8 | Number of `u64` words per DB entry (Standard: 4). |
| **Records** | | **Count * 40** | List of delta updates. |

### Delta Record Structure

Each record represents a change to a specific Account.

| Field | Type | Size (Bytes) | Description |
|-------|------|--------------|-------------|
| AccountIndex | `u64` | 8 | The canonical index of the account in `database.bin`. |
| Delta | `[u64; 4]` | 32 | The XOR difference (`OldValue ^ NewValue`) to be applied. |

## Client Update Logic

To process a delta file:

1. Read `Count`.
2. Iterate `Count` times:
   - Read `AccountIndex`, `Delta`.
   - Calculate `HintID = Client_IPRF(AccountIndex)`.
   - Update local hint: `Hint[HintID] ^= Delta`.

## Notes

- **Atomicity**: A block may produce multiple updates for the same `HintSetID` (if multiple accounts in that set changed). The client must apply **all** of them.
- **Ordering**: Order within the file does not matter (XOR is commutative), but files must be processed in block order (e.g., 100 -> 101 -> 102).
- **Alignment**: All values are 8-byte aligned and Little Endian.
