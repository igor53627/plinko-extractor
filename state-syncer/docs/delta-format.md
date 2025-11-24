# Plinko Delta File Format

The `state-syncer` service produces per-block delta files (e.g., `delta-23237685.bin`) that allow PIR clients to update their local hints without re-downloading the database.

## File Structure

The file is a binary stream encoded in Little Endian (LE).

| Field | Type | Size (Bytes) | Description |
|-------|------|--------------|-------------|
| **Header** | | **16** | |
| Count | `u64` | 8 | Number of delta records in this file. |
| EntryLength | `u64` | 8 | Number of `u64` words per DB entry (Standard: 4). |
| **Records** | | **Count * 48** | List of delta updates. |

### Delta Record Structure

Each record represents a change to a specific PIR Hint Set.

| Field | Type | Size (Bytes) | Description |
|-------|------|--------------|-------------|
| HintSetID | `u64` | 8 | The ID of the Hint Set (Row) that needs updating. Derived via IPRF. |
| IsBackup | `u64` | 8 | `1` if this update applies to the Backup Hint Set, `0` for Primary. |
| Delta | `[u64; 4]` | 32 | The XOR difference (`OldValue ^ NewValue`) to be applied to the hint. |

## Client Update Logic

To process a delta file:

1. Read `Count`.
2. Iterate `Count` times:
   - Read `HintSetID`, `IsBackup`, `Delta`.
   - Check if the client is storing the hint for `HintSetID`.
   - If yes, update local hint: `Hint[HintSetID] ^= Delta`.

## Notes

- **Atomicity**: A block may produce multiple updates for the same `HintSetID` (if multiple accounts in that set changed). The client must apply **all** of them.
- **Ordering**: Order within the file does not matter (XOR is commutative), but files must be processed in block order (e.g., 100 -> 101 -> 102).
- **Alignment**: All values are 8-byte aligned and Little Endian.
