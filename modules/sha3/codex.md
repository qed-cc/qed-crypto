<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- Copyright (c) 2025 Rhett Creighton -->

# SHA3 Library – High-Performance Usage Guide

The SHA3 library provides:
  • Single-shot and streaming SHA-3 (224/256/384/512) and SHAKE (128/256)
  • Bulk-parallel SHA-3 hashing of N equal-length messages with AVX2/AVX-512 multi-buffer kernels
  • A fixed 4-ary Merkle-tree builder over 32-byte leaves using SHA3-256 and a persistent thread pool (~40 MH/s)

## Build

  git submodule update --init --recursive
  mkdir build && cd build
  cmake -DCMAKE_BUILD_TYPE=Release \
        -DSHA3_BUILD_EXAMPLES=ON ..
  make -j$(nproc)

## Core APIs

```c
#include "sha3.h"

// One-shot hash
int sha3_hash(
    sha3_hash_type type,
    const void     *data,
    size_t          len,
    void           *digest,
    size_t          digest_size
);

// Streaming (init/update/final)
int sha3_init  (sha3_ctx *ctx, sha3_hash_type type);
int sha3_update(sha3_ctx *ctx, const void *data, size_t len);
int sha3_final (sha3_ctx *ctx, void *digest, size_t digest_size);

// Bulk-parallel equal-length messages (len <= block size)
int sha3_hash_parallel_len(
    sha3_hash_type type,
    const void    *data,
    size_t         len,
    void          *output,
    size_t         n
);

// Fast-path for exactly 64-byte messages
int sha3_hash_parallel(
    sha3_hash_type type,
    const void    *data,  // n × 64 bytes
    void          *output,
    size_t         n
);

// Bulk-parallel with on-the-fly padding (msg_len <= block size)
int sha3_hash_parallel_eqlen(
    sha3_hash_type type,
    const void    *data,
    size_t         msg_len,
    void          *output,
    size_t         n
);
```

## 4-ary Merkle Tree (32-byte leaves)

```c
// Each leaf is 32 bytes; Merkle root is 32 bytes
#define MERKLE_LEAF_SIZE 32
int sha3_merkle_tree4_32(
    const uint8_t *leaves,     // num_leaves × 32 bytes
    size_t         num_leaves,
    uint8_t       *root        // 32-byte output
);
```

• Spawns a persistent pool of worker threads once
• Each level: pack 4×32 B children into 136 B blocks, pad (0x06…0x80), and hash via AVX-512×8
• Two-phase pthread_barrier per level
• End-to-end throughput ~40–45 MH/s on 16 cores

## Examples
  • `sha3_parallel_benchmark` – raw parallel hashing (64 B messages)
  • `sha3_merkle_benchmark`  – 4-ary Merkle-tree build benchmark

## Tests
  • `test_sha3`   – verify SHA-3 outputs
  • `test_merkle` – verify root for N=1,2,4 leaves

## Introspection
  size_t sha3_get_digest_size(sha3_hash_type type);
  size_t sha3_get_block_size (sha3_hash_type type);
  const char *sha3_version(void);

## License