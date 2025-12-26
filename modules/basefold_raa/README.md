# BaseFold RAA - Optimized Zero-Knowledge Proof System

## Overview

BaseFold RAA combines the BaseFold sumcheck protocol with Reed-Solomon RAA (Randomized Affine Aggregation) encoding to achieve optimal performance for zero-knowledge proofs in the gate_computer framework.

### Key Features

- **122-bit post-quantum security** (effective soundness)
- **~150ms proof generation** for SHA3-256 (192,086 gates)
- **~190KB proof size** with 320 queries
- **Zero-knowledge privacy** with polynomial masking
- **Linear-time encoding** with RAA systematic codes
- **Multi-threaded** proof generation with OpenMP

## Technical Details

### Architecture

1. **Sumcheck Protocol**: Reduces multilinear polynomial claims to univariate evaluation
2. **Binary NTT**: Converts between polynomial representations using additive FFT
3. **RAA Encoding**: Linear-time systematic encoding with good error correction
4. **Merkle Commitment**: 4-ary tree with SHA3-256 for cryptographic binding

### Security Properties

- **Soundness**: 122 bits (limited by sumcheck in GF(2^128))
- **Completeness**: 100% (honest proofs always verify)
- **Zero-Knowledge**: Perfect on evaluation domain
- **Post-Quantum**: No discrete log assumptions

## API Usage

```c
#include "basefold_raa.h"

// Configure proof system
basefold_raa_config_t config = {
    .num_variables = 18,  // log2(witness_size)
    .security_level = 128,
    .enable_zk = 1,       // Enable zero-knowledge
    .num_threads = 4      // OpenMP threads
};

// Generate proof
basefold_raa_proof_t proof = {0};
int ret = basefold_raa_prove(witness, &config, &proof);
if (ret != 0) {
    // Handle error
}

// Verify proof
if (basefold_raa_verify(&proof, &config) == 0) {
    printf("Proof verified!\n");
}

// Clean up
basefold_raa_proof_free(&proof);
```

## Building

The module is built as part of the gate_computer project:

```bash
mkdir build && cd build
cmake -DCMAKE_BUILD_TYPE=Release -DBUILD_BASEFOLD_RAA=ON ..
make basefold_raa
```

## Performance

| Circuit | Gates | Proof Time | Proof Size | Verification |
|---------|-------|------------|------------|--------------|
| SHA3-256 | 192K | ~150ms | ~190KB | ~7ms |
| SHA2-256 | 90K | ~70ms | ~95KB | ~4ms |
| Keccak-f | 38K | ~30ms | ~45KB | ~2ms |

## Security Considerations

1. **Always use secure randomness** - The implementation requires `/dev/urandom` or `getrandom()`
2. **Enable zero-knowledge** for privacy-sensitive applications
3. **Use 320 queries minimum** for 122-bit security
4. **Domain separation** is enforced in Fiat-Shamir transform

## Implementation Status

✅ **Production Ready** with the following features:
- Cryptographically secure randomness
- Zero-knowledge polynomial masking
- Binary NTT integration
- Merkle tree authentication paths
- Comprehensive error handling
- Multi-threaded optimization

## Testing

Run the test suite:
```bash
cd build
ctest -R basefold_raa --output-on-failure
```

## References

- [BaseFold: Efficient Field-Agnostic Polynomial Commitment Schemes](https://eprint.iacr.org/2023/1143)
- [Fast Reed-Solomon Interactive Oracle Proofs of Proximity](https://eccc.weizmann.ac.il/report/2017/134/)
- Binary NTT: Lin-Chung-Han algorithm for additive FFT in binary fields

## License

Apache-2.0 - See LICENSE file for details.