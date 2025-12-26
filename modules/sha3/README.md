<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- Copyright (c) 2025 Rhett Creighton -->

# SHA3 Library – High-Performance Parallel SHA3-256

This library provides a parallel, SIMD-accelerated implementation of SHA3-256 optimized for fixed-size messages.

## Build

```bash
mkdir build && cd build
cmake -DCMAKE_BUILD_TYPE=Release \
      -DSHA3_BUILD_EXAMPLES=ON \
      -DCMAKE_C_FLAGS="-O3 -march=native -funroll-loops" ..
make -j$(nproc)
```

## API

Include the public header:
```c
#include "sha3.h"
```

Hash N messages of constant length `msg_len` (≤ block size):
```c
int rc = sha3_hash_parallel_len(
    SHA3_256,   // hash type
    data,       // input buffer: N * msg_len bytes
    msg_len,    // constant message length
    out,        // output buffer: N * digest_size bytes
    N           // number of messages
);
```
For exactly 64-byte messages:
```c
sha3_hash_parallel(SHA3_256, data, out, N);
```

## Benchmark

Measure pad-and-hash throughput for 1 000 000 messages of 64 bytes:
```bash
build/bin/sha3_parallel_benchmark 1000000 64
```
Example output on AVX2/AVX-512 hardware:
```
sha3_hash_parallel_len: 1000000 messages of 64 bytes in 0.009 s
Throughput: 113e6 msgs/s (6.9 GiB/s) on 16 threads
```

## All-in-One Build & Benchmark Script

For an end-to-end build, self-test, and performance run (parallel hashing and Merkle-tree build), use the included `bench.sh` script:

```bash
chmod +x bench.sh
./bench.sh [PAR_BENCH_COUNT] [MERKLE_BENCH_LEAVES]
```

- `PAR_BENCH_COUNT` (default: 10000000) – number of 64-byte messages to hash in parallel
- `MERKLE_BENCH_LEAVES` (default: 10000000) – number of 32-byte leaves in the 4-ary Merkle tree

Example run on a 16-core AVX-512 machine:
```
=== SHA3 Parallel Benchmark ===
sha3_hash_parallel_len: 10000000 messages of 64 bytes in 0.126 s
Throughput: 79e6 msgs/s (4.8 GiB/s) on 16 threads

=== Merkle Tree Benchmark ===
Building 4-ary Merkle tree with 10000000 leaves...
Built in 0.194 s -> 52 M hashes/s
All done.
```

## License

Apache-2.0