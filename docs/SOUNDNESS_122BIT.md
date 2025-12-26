/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

# Understanding the 122-bit Soundness in BaseFold

## Overview

Both BaseFold and BaseFold RAA provide **122 bits of effective soundness**, not 128 bits. This document explains why this is still cryptographically secure and what it means for users.

## The Mathematics

### Sumcheck Protocol Soundness

The sumcheck protocol is the core of BaseFold's security. For a multilinear polynomial over GF(2^128):

- **Field size**: |F| = 2^128
- **Gate degree**: d = 3 (AND/XOR gates in our circuits)
- **Number of rounds**: n = 18 (for SHA3-256 with 2^18 = 262,144 gates)

The soundness error is bounded by:
```
ε ≤ n × d / |F| = 18 × 3 / 2^128 ≈ 2^-122
```

This gives us **122 bits of soundness**.

### Why Not 128 Bits?

To achieve 128 bits from sumcheck alone, we would need one of:
1. Larger field (e.g., GF(2^256)) - major performance penalty
2. Lower degree gates (d=2) - limits circuit expressiveness  
3. Fewer rounds (smaller circuits) - not practical for real applications

## Is 122 Bits Secure?

**YES.** Here's why:

### Computational Infeasibility
- 2^122 operations would take billions of years on all computers combined
- Well above the 80-bit threshold considered secure
- Higher than many deployed systems (e.g., 112-bit RSA-2048 equivalent)

### Comparison with Standards
- NIST requires 112 bits for "acceptable" security through 2030
- 128 bits is for "long-term" security (30+ years)
- Our 122 bits exceeds current requirements

### Post-Quantum Security
- No discrete logarithm assumptions
- Quantum computers provide at most square-root speedup (Grover)
- Effective quantum security: ~61 bits (still infeasible)

## What This Means for Users

### For Most Applications
- 122 bits is more than sufficient
- No practical attacks possible
- Post-quantum secure

### For Ultra-High Security Requirements
If you absolutely need 128+ bits:
1. Use BaseFold with sumcheck composition (run 2 instances)
2. Accept slightly larger proofs (~7KB additional)
3. Or increase FRI queries to 320 (still limited by sumcheck)

## Configuration Options

### Standard (122-bit soundness)
```c
basefold_raa_config_t config = {
    .num_variables = 18,
    .security_level = 128,  // Target (actual: 122)
    .enable_zk = 1,
    .num_queries = 100      // Sufficient for sumcheck limit
};
```

### With Sumcheck Composition (244-bit soundness)
```c
// Future implementation
basefold_raa_config_t config = {
    .num_variables = 18,
    .security_level = 128,
    .enable_zk = 1,
    .num_queries = 100,
    .sumcheck_instances = 2  // Run twice for 2^-244 error
};
```

## Summary

- BaseFold provides **122 bits of effective soundness**
- This is **cryptographically secure** for all practical purposes
- The limitation comes from fundamental protocol parameters
- Post-quantum secure with no discrete log assumptions

For the vast majority of applications, 122 bits provides excellent security with optimal performance.