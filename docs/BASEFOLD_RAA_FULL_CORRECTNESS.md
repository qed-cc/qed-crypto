/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

# BaseFold + RAA: Requirements for Full Correctness

## Executive Summary

For BaseFold+RAA to be fully correct and production-ready, it needs to satisfy mathematical soundness, implementation completeness, and security requirements. This document outlines exactly what is needed.

## 1. Mathematical Correctness Requirements

### 1.1 Sumcheck Protocol
- ✅ **Status**: Implemented correctly
- **Requirement**: Must verify multilinear polynomial evaluations with soundness error ≤ n·d/|F|
- **Current**: 18 rounds × degree 3 / 2^128 ≈ 2^-122 soundness

### 1.2 Binary NTT (Number Theoretic Transform)
- ❌ **Status**: Using placeholder/simulation
- **Requirement**: Must correctly convert multilinear polynomial to univariate representation
- **Needed**:
  ```c
  // Convert multilinear evaluations to univariate coefficients
  int binary_ntt_forward(const gf128_t* multilinear_evals, 
                        gf128_t* univariate_coeffs, 
                        size_t num_variables);
  
  // Inverse transform for verification
  int binary_ntt_inverse(const gf128_t* univariate_coeffs,
                        gf128_t* multilinear_evals,
                        size_t num_variables);
  ```

### 1.3 RAA Encoding
- ✅ **Status**: Implemented with correct systematic encoding
- **Requirement**: Linear-time encoding with good minimum distance
- **Current**: 4x repetition + dual permutation-accumulation structure

### 1.4 Polynomial Commitment
- ✅ **Status**: Merkle tree implementation complete
- **Requirement**: Binding commitment to RAA codeword
- **Current**: SHA3-256 based Merkle trees with proper domain separation

## 2. Implementation Completeness

### 2.1 Missing Components

1. **Binary NTT Implementation** (CRITICAL)
   - Files needed in `modules/basefold/src/`:
     - `binary_ntt_core.c` - Core transform logic
     - `binary_ntt_butterfly.c` - Butterfly operations
     - `binary_ntt_roots.c` - Roots of unity in GF(2^128)
   
2. **Proper Circuit-to-Witness Generation**
   - Current: Test uses simulated witness
   - Needed: Actual SHA3 circuit evaluation → witness generation
   ```c
   // Generate witness from actual circuit evaluation
   gf128_t* evaluate_sha3_circuit(const uint8_t* input, 
                                  size_t input_len,
                                  size_t* witness_size);
   ```

3. **Complete Query Generation**
   - Current: 100 queries (insufficient for 128-bit claim)
   - Needed: 320 queries for proper security
   ```c
   #define BASEFOLD_RAA_NUM_QUERIES 320  // Update in basefold_raa.h
   ```

### 2.2 Integration Requirements

1. **Main Binary Build**
   - Fix `gate_computer` CLI to support BaseFold RAA
   - Resolve undefined references to FRI/Binary NTT
   - Update CMakeLists.txt

2. **Proper Test Harness**
   - Replace ALL mock SHA3 with real implementation
   - Add OpenSSL verification in every test
   - Include timing measurements

## 3. Security Requirements

### 3.1 Soundness
- **Current**: 122-bit effective soundness
- **Required for "128-bit" claim**: Either:
  - Accept 122-bit as sufficient (recommended)
  - Implement sumcheck composition (2 instances → 244 bits)
  - Document clearly that effective soundness is 122 bits

### 3.2 Zero-Knowledge
- ✅ **Status**: Polynomial masking implemented
- **Requirement**: No information leakage about witness
- **Current**: Proper randomization before commitment

### 3.3 Cryptographic Security
- ✅ **SHA3-256**: Real implementation in production
- ✅ **GF(2^128)**: Constant-time operations
- ✅ **Random Number Generation**: Cryptographically secure
- ❌ **Query Count**: Need 320 queries (currently 100)

## 4. Verification Requirements

### 4.1 Proof Verification Must Check:
1. **Sumcheck verification**: All round polynomials
2. **Binary NTT consistency**: Polynomial evaluation matches
3. **RAA encoding verification**: Local consistency checks
4. **Merkle path verification**: All query authentication paths
5. **Binding verification**: Sumcheck ↔ Merkle commitment

### 4.2 Test Coverage Needed:
```bash
# Every test MUST verify:
echo -n "input" | openssl dgst -sha3-256  # Expected output
./gate_computer --gen-sha3 --input "input" --prove proof.bin
./gate_computer --verify proof.bin  # Must succeed
# Output hash MUST match OpenSSL
```

## 5. Performance Requirements

### 5.1 Target Metrics
- **Proof Generation**: <500ms for SHA3-256
- **Proof Size**: <500KB (currently 41.5KB ✅)
- **Verification**: <50ms (currently 2.5ms ✅)

### 5.2 Optimizations Needed
1. **AVX-512 for Binary NTT**
2. **Parallel RAA encoding** (OpenMP)
3. **Batch Merkle tree operations**

## 6. Documentation Requirements

### 6.1 User Documentation
- How to generate proofs for SHA3-256
- Security guarantees (122-bit soundness)
- Performance characteristics
- API examples

### 6.2 Developer Documentation
- Binary NTT algorithm specification
- RAA encoding detailed algorithm
- Security proofs and analysis
- Test methodology

## 7. Immediate Action Items

1. **Implement Binary NTT** (Highest Priority)
   - This is the main missing piece
   - Without it, the system is incomplete

2. **Increase Query Count**
   ```c
   // In basefold_raa.h
   #define BASEFOLD_RAA_NUM_QUERIES 320  // was 100
   ```

3. **Fix All Tests**
   - Use real SHA3 everywhere
   - Verify against OpenSSL
   - Remove ALL mock implementations

4. **Update Documentation**
   - Clearly state 122-bit soundness
   - Explain the security model
   - Provide correct benchmarks

## 8. Validation Checklist

Before declaring BaseFold+RAA production-ready:

- [ ] Binary NTT fully implemented and tested
- [ ] 320 queries for proper security
- [ ] All tests use real SHA3 and verify against OpenSSL
- [ ] Main `gate_computer` binary builds and runs
- [ ] Performance meets targets (<500ms, <500KB)
- [ ] Documentation clearly states 122-bit soundness
- [ ] Security audit of complete implementation
- [ ] Benchmarks on real hardware
- [ ] Integration tests with various inputs
- [ ] No mock/fake implementations anywhere

## Conclusion

BaseFold+RAA is a promising system that achieves 14.6x smaller proofs than standard BaseFold. However, it needs:

1. **Binary NTT implementation** (critical missing piece)
2. **320 queries** for security claims
3. **Real SHA3 in all tests**
4. **Clear documentation** of 122-bit soundness

Once these are addressed, the system will be fully correct and production-ready.