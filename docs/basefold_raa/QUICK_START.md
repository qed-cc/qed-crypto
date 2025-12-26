/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

# BaseFold RAA Quick Start Guide

## Overview

BaseFold RAA is a production-ready zero-knowledge proof system that combines BaseFold's efficient sumcheck protocol with Random Access Accumulation (RAA) encoding. It provides:

- **128-bit post-quantum security**
- **40KB proof sizes** (14.6x smaller than standard BaseFold)
- **150ms proof generation** for SHA3-256 (192K gates)
- **Zero-knowledge privacy** protection

## Installation

```bash
# Clone the repository
git clone https://github.com/RhettCreighton/gate_computer.git
cd gate_computer

# Build with BaseFold RAA support
mkdir build && cd build
cmake -DCMAKE_BUILD_TYPE=Release -DBUILD_BASEFOLD_RAA=ON ..
make -j$(nproc)
```

## Basic Usage

### Command Line Interface

```bash
# Generate SHA3-256 circuit and create proof
./build/bin/gate_computer --gen-sha3-256 --input-text "hello world" --prove proof.bfp

# Verify the proof
./build/bin/gate_computer --verify proof.bfp

# Generate proof with custom parameters
./build/bin/gate_computer --gen-sha3-256 --input-hex deadbeef --prove proof.bfp --threads 8
```

### C API Example

```c
#include "basefold_raa.h"
#include <stdio.h>

int main() {
    // Configure the proof system
    basefold_raa_config_t config = {
        .num_variables = 18,    // 2^18 = 262,144 gates
        .security_level = 128,  // 128-bit security
        .enable_zk = 1,         // Enable zero-knowledge
        .num_threads = 4        // Use 4 threads
    };
    
    // Create witness (evaluation of circuit on inputs)
    size_t witness_size = 1ULL << config.num_variables;
    gf128_t* witness = calloc(witness_size, sizeof(gf128_t));
    
    // ... populate witness with circuit evaluation ...
    
    // Generate proof
    basefold_raa_proof_t proof = {0};
    int result = basefold_raa_prove(witness, &config, &proof);
    if (result != 0) {
        fprintf(stderr, "Proof generation failed\n");
        return 1;
    }
    
    printf("Proof generated: %zu bytes\n", proof.size);
    
    // Verify proof
    result = basefold_raa_verify(&proof, &config);
    if (result == 0) {
        printf("Proof verified successfully!\n");
    } else {
        printf("Proof verification failed\n");
    }
    
    // Cleanup
    basefold_raa_proof_free(&proof);
    free(witness);
    
    return 0;
}
```

## Circuit Formats

BaseFold RAA supports two circuit formats:

### 1. Binary Format (Recommended)
Compact binary representation for production use:
```c
// Load circuit from binary file
circuit_t* circuit = circuit_load_binary("sha3_256.circuit");
```

### 2. Text Format
Human-readable format for debugging:
```
# SHA3-256 Circuit
num_inputs 512
num_outputs 256
num_gates 192086

# Gate definitions
gate 0: AND 1 2 -> 3
gate 1: XOR 3 4 -> 5
...
```

## Performance Benchmarks

| Circuit | Gates | Proof Time | Proof Size | Verification Time |
|---------|-------|------------|------------|-------------------|
| SHA3-256 | 192K | 142ms | 41.5KB | 18ms |
| SHA2-256 | 130K | 98ms | 38.2KB | 16ms |
| AES-128 | 45K | 35ms | 32.1KB | 12ms |

## Advanced Features

### Multi-threaded Proving
```c
config.num_threads = 8;  // Use 8 threads for parallel computation
```

### Custom Security Levels
```c
config.security_level = 256;  // 256-bit security (larger proofs)
```

### Streaming Mode
For very large circuits that don't fit in memory:
```c
config.streaming_mode = 1;
config.stream_chunk_size = 1 << 20;  // 1M gates per chunk
```

## Troubleshooting

### Out of Memory
- Enable streaming mode for circuits > 10M gates
- Reduce thread count to lower memory usage

### Slow Performance
- Ensure you built with `-DCMAKE_BUILD_TYPE=Release`
- Check CPU supports AVX-512 with `./build/tools/check_cpu`
- Increase thread count up to number of CPU cores

### Verification Failures
- Ensure witness is computed correctly
- Check circuit format is valid
- Verify input/output constraints are satisfied

## Next Steps

- See [DEVELOPER_GUIDE.md](DEVELOPER_GUIDE.md) for implementation details
- Read [../SECURITY.md](../SECURITY.md) for security analysis
- Check [examples/](../../examples/) for more code samples