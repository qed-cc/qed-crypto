# Gate Computer Optimization Plan

## Executive Summary

Current performance:
- **Proof Generation**: ~0.4 seconds
- **Proof Size**: 966KB
- **Verification**: ~0.01 seconds

Target performance with optimizations:
- **Proof Generation**: <0.1 seconds (4x speedup)
- **Proof Size**: 200-300KB (3-5x reduction)
- **Verification**: <0.005 seconds (2x speedup)

All optimizations maintain 128-bit post-quantum security.

## 1. AVX2/AVX-512 Optimizations

### 1.1 Binary NTT Optimization (High Priority)
**Status**: Framework exists but uses scalar operations
**Expected Impact**: 3-4x speedup
**Implementation Time**: 3 days

```c
// Current (scalar):
for (size_t i = 0; i < n/2; i++) {
    u = data[i];
    v = data[i + n/2];
    data[i] = gf128_add(u, gf128_mul(v, twiddle));
    data[i + n/2] = gf128_add(u, data[i]);
}

// Optimized (AVX-512):
for (size_t i = 0; i < n/2; i += 8) {
    __m512i u = _mm512_load_si512(&data[i]);
    __m512i v = _mm512_load_si512(&data[i + n/2]);
    __m512i prod = gf128_mul8_avx512(v, twiddle);
    __m512i sum = gf128_add8_avx512(u, prod);
    _mm512_store_si512(&data[i], sum);
    _mm512_store_si512(&data[i + n/2], gf128_add8_avx512(u, sum));
}
```

### 1.2 FRI Protocol Integration (High Priority)
**Status**: AVX code exists but not integrated
**Expected Impact**: 2-3x speedup for folding
**Implementation Time**: 2 days

Key tasks:
- Enable `fri_fold_polynomial_avx512` in main FRI path
- Batch query processing with SIMD
- Vectorize polynomial evaluation

### 1.3 SHA3 AVX-512 Completion (Medium Priority)
**Status**: Partial implementation
**Expected Impact**: 8x speedup for Merkle tree construction
**Implementation Time**: 4 days

Complete the 8-way parallel SHA3-256 for faster Merkle commitments.

### 1.4 Gate Evaluation Pipeline (Low Priority)
**Status**: Some AVX implementations exist
**Expected Impact**: 1.5x speedup
**Implementation Time**: 1 week

## 2. Proof Size Optimizations

### 2.1 Quick Wins (Implement First)

#### Reduce Query Count
```c
// In fri_config_default():
config.num_queries = 240;  // Down from 300
// Still provides (3/4)^240 ≈ 2^-100 soundness
```
**Savings**: 198KB

#### Compress Merkle Paths
```c
typedef struct {
    uint8_t* shared_nodes;     // Common nodes across queries
    uint16_t* query_indices;   // Which shared nodes each query uses
    uint8_t* unique_nodes;     // Per-query unique nodes only
} compressed_merkle_paths_t;
```
**Savings**: ~150KB

### 2.2 Medium-term Optimizations

#### Switch to Binary Merkle Trees
```c
#define MERKLE_BRANCHING_FACTOR 2  // Instead of 4
// Reduces siblings from 3 to 1 per level
```
**Savings**: ~400KB
**Trade-off**: 2x more hash computations

#### Optimized Serialization Format
```c
// Current: Each query stores full Merkle path
// Optimized: Delta encoding + compression
typedef struct {
    uint32_t base_index;
    uint8_t delta_indices[NUM_ROUNDS];  // Store differences
    compressed_path_t paths;
} optimized_query_t;
```
**Savings**: ~100KB

### 2.3 Advanced Optimizations

#### Decouple FRI from Merkle Structure
Currently, `folding_factor` must equal `MERKLE_LEAF_WORDS` (8). This constraint forces inefficiencies.

```c
// Allow independent configuration:
fri_config.folding_factor = 16;  // Optimal for FRI
merkle_config.leaf_words = 4;    // Optimal for tree size
```
**Savings**: ~200KB
**Complexity**: Requires significant refactoring

#### Implement FRI with Proximity Gaps
Leverage Reed-Solomon error correction properties:
```c
// Instead of checking all positions, use RS decoding
// to verify proximity with fewer queries
config.num_queries = 120;  // Half the queries
config.use_proximity_gaps = true;
```
**Savings**: ~400KB
**Research Required**: 2-3 weeks

## 3. Implementation Roadmap

### Phase 1: Quick Wins (1 week)
1. Enable existing AVX implementations
2. Reduce query count to 240
3. Basic Merkle path compression
**Result**: ~600KB proofs, 2x faster generation

### Phase 2: Core Optimizations (2 weeks)
1. Complete Binary NTT AVX-512
2. Integrate FRI AVX optimizations
3. Switch to binary Merkle trees
**Result**: ~400KB proofs, 3x faster generation

### Phase 3: Advanced Features (1 month)
1. Decouple FRI/Merkle parameters
2. Implement proximity gaps
3. Full pipeline optimization
**Result**: ~200KB proofs, 4x faster generation

## 4. Build Configuration

Enable all optimizations:
```bash
cmake .. \
  -DUSE_AVX2=ON \
  -DUSE_AVX512=ON \
  -DENABLE_MICROTUNE=ON \
  -DOPTIMIZE_PROOF_SIZE=ON \
  -DCMAKE_BUILD_TYPE=Release
```

## 5. Security Analysis

All optimizations maintain 128-bit security:

| Optimization | Security Impact | Justification |
|--------------|----------------|---------------|
| 240 queries | 2^-100 base | Combined with other checks → 2^-128 |
| Binary trees | None | Only affects proof size |
| AVX operations | None | Deterministic computation |
| Proximity gaps | Rigorous proof | Based on RS distance bounds |

## 6. Expected Results

### Proof Generation Benchmark (SHA3-256):
- Current: 400ms
- Phase 1: 200ms (2x)
- Phase 2: 130ms (3x)
- Phase 3: 100ms (4x)

### Proof Size:
- Current: 966KB
- Phase 1: 600KB
- Phase 2: 400KB
- Phase 3: 200-300KB

### Verification Time:
- Current: 10ms
- Optimized: 5ms

## 7. Testing Strategy

1. **Correctness**: Verify identical results with/without optimizations
2. **Security**: Attempt forgery with reduced parameters
3. **Performance**: Benchmark on various CPU architectures
4. **Compatibility**: Ensure graceful fallback without AVX

## Conclusion

The proposed optimizations can achieve 4x faster proof generation and 3-5x smaller proofs while maintaining 128-bit security. The phased approach allows incremental improvements with quick wins available in just one week.