# BaseFold RAA Developer Guide

## Overview

BaseFold RAA is a hybrid proof system that combines BaseFold's sumcheck protocol with RAA (Randomized Affine Aggregation) encoding to achieve smaller proofs while maintaining 128-bit post-quantum security.

## Key Features

- **20% faster** proof generation than standard BaseFold
- **14.6x smaller** proofs (41.5 KB vs 606 KB)  
- **128-bit post-quantum security**
- **Zero-knowledge** via polynomial masking
- **Pre-generated permutations** for optimal performance

## Quick Start

### 1. Build the System

```bash
mkdir build && cd build
cmake -DCMAKE_BUILD_TYPE=Release -DBUILD_BASEFOLD_RAA=ON ..
make -j$(nproc)
```

### 2. Generate SHA3-256 Circuit

```bash
# Generate circuit and witness for SHA3-256
./build/bin/gate_computer --gen-sha3-256 --input-text "hello world" --output circuit.txt
```

### 3. Generate Proof

```c
#include "basefold_raa.h"

// Load pre-generated permutations (done once at startup)
basefold_raa_global_init();

// Configure proof system
basefold_raa_config_t config = {
    .num_variables = 16,        // For 2^16 witness size
    .security_level = 128,      
    .enable_zk = 1,            // Enable zero-knowledge
    .num_threads = 4           // Parallel execution
};

// Generate proof
basefold_raa_proof_t proof = {0};
int ret = basefold_raa_prove(witness, &config, &proof);
if (ret == 0) {
    printf("Proof generated: %zu bytes\n", 
           basefold_raa_proof_size(&config));
}
```

### 4. Verify Proof

```c
// Verify the proof
int valid = basefold_raa_verify(&proof, &config);
if (valid == 0) {
    printf("Proof is valid!\n");
}

// Clean up
basefold_raa_proof_free(&proof);
```

## Architecture

### Proof Generation Pipeline

1. **Sumcheck Protocol** (63% of time)
   - Reduces multilinear polynomial to univariate
   - Performs `log(witness_size)` rounds
   - Each round: compute g₀, g₁, commit, get challenge

2. **Binary NTT** (16% of time)
   - Converts sumcheck result to univariate coefficients
   - Enables efficient polynomial commitment

3. **RAA Encoding** (11% of time)
   - Two-stage encoding process:
     - Stage 1: Repetition → Permutation₁ → Accumulation
     - Stage 2: Permutation₂ → Accumulation
   - Uses pre-generated permutations

4. **Commitment & Queries** (10% of time)
   - Merkle tree commitment to RAA codeword
   - Generate 200 query positions via Fiat-Shamir
   - Create opening proofs

### Pre-generated Permutations

The system uses two permutations (P1 and P2) that are generated once and loaded at startup:

```c
// At application startup
basefold_raa_global_init();  // Loads pre-generated permutations

// The permutations are stored in:
// - ~/.gate_computer/raa_perms_256k.bin (for 64K witness)
// - Generated using cryptographic Fisher-Yates shuffle
// - 4MB total (2 × 262,144 × 8 bytes)
```

## Performance Characteristics

### Timing Breakdown (142.5ms total)
- Sumcheck protocol: 90ms (63.2%)
- Binary NTT: 22.5ms (15.8%)
- RAA encoding: 15ms (10.5%)
- Commitment: 7.5ms (5.3%)
- Query generation: 7.5ms (5.3%)

### Proof Size (41.5 KB total)
- Sumcheck data: 3.4 KB (8.1%)
- Query responses: 4.9 KB (11.8%)
- Merkle paths: 32.8 KB (79.1%)
- Metadata: 0.4 KB (1.0%)

## API Reference

### Core Functions

```c
// Initialize global state (call once at startup)
int basefold_raa_global_init(void);

// Generate proof
int basefold_raa_prove(
    const gf128_t* witness,
    const basefold_raa_config_t* config,
    basefold_raa_proof_t* proof
);

// Verify proof
int basefold_raa_verify(
    const basefold_raa_proof_t* proof,
    const basefold_raa_config_t* config
);

// Get proof size estimate
size_t basefold_raa_proof_size(const basefold_raa_config_t* config);

// Free proof memory
void basefold_raa_proof_free(basefold_raa_proof_t* proof);
```

### Configuration Structure

```c
typedef struct {
    size_t num_variables;    // log2(witness_size)
    size_t security_level;   // Target security bits (128)
    int enable_zk;          // Enable zero-knowledge
    int num_threads;        // OpenMP thread count
} basefold_raa_config_t;
```

## Example: Complete SHA3-256 Proof

```c
#include <stdio.h>
#include <stdlib.h>
#include "basefold_raa.h"
#include "sha3.h"

int main() {
    // Initialize system
    basefold_raa_global_init();
    
    // Generate SHA3-256 witness
    const char* input = "hello world";
    size_t witness_size = 65536;  // 2^16
    gf128_t* witness = generate_sha3_witness(input, witness_size);
    
    // Configure
    basefold_raa_config_t config = {
        .num_variables = 16,
        .security_level = 128,
        .enable_zk = 1,
        .num_threads = 4
    };
    
    // Prove
    basefold_raa_proof_t proof = {0};
    if (basefold_raa_prove(witness, &config, &proof) == 0) {
        printf("Proof generated: %zu bytes\n", 
               basefold_raa_proof_size(&config));
        
        // Verify
        if (basefold_raa_verify(&proof, &config) == 0) {
            printf("Proof verified!\n");
        }
    }
    
    // Cleanup
    basefold_raa_proof_free(&proof);
    free(witness);
    
    return 0;
}
```

## Troubleshooting

### Common Issues

1. **"Failed to load permutations"**
   - Run `basefold_raa_gen_perms` to generate permutation files
   - Check `~/.gate_computer/` directory permissions

2. **Performance lower than expected**
   - Ensure Release build: `-DCMAKE_BUILD_TYPE=Release`
   - Check OpenMP is enabled: `-fopenmp`
   - Verify AVX2/AVX512 support: `cat /proc/cpuinfo | grep avx`

3. **Proof verification fails**
   - Ensure witness is correctly generated
   - Check that config matches between prove and verify
   - Verify permutations are loaded correctly

## Security Considerations

- Always use `enable_zk = 1` for privacy-sensitive applications
- The system provides 128-bit post-quantum security
- Soundness error: 2^-200 with 200 queries
- Uses SHA3-256 for all cryptographic commitments

## Further Reading

- [Performance Analysis](BASEFOLD_RAA_FINAL_PERFORMANCE.md)
- [Technical Specification](../../spec-documentation/BASEFOLD_RAA_SPECIFICATION.md)
- [Security Analysis](../../security/BASEFOLD_RAA_SECURITY.md)