/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

# PoS Optimization Implementation Issues

## Summary of Issues Found

After thorough review of the PoS optimization implementation, I've identified the following incomplete items, missing pieces, and issues that need attention:

## 1. API Mismatches with BaseFold RAA

### Issue
Multiple files are calling basefold_raa functions with incorrect signatures:

- **hierarchical_vrf.c:134**: Calls `basefold_raa_prove` with 3 arguments, but actual function expects `gf128_t*` witness and `basefold_raa_config_t*`
- **early_finality.c:395**: Same issue - calling with wrong signature
- **streaming_dag_impl.c:170**: Calls non-existent `basefold_raa_circular_prove`

### Files Affected
- `src/hierarchical_vrf.c`
- `src/early_finality.c` 
- `src/streaming_dag_impl.c`
- `src/recursive_committee.c`
- `src/recursive_stark.c`

### Fix Required
Need to update all calls to match the actual basefold_raa API:
```c
// Current (wrong):
proof = basefold_raa_prove(&witness, sizeof(witness), "tag");

// Should be:
basefold_raa_config_t config = {
    .num_variables = log2(witness_size),
    .security_level = 122,
    .enable_zk = 1,
    .num_threads = 0
};
basefold_raa_proof_t proof;
basefold_raa_prove(witness_gf128, &config, &proof);
```

## 2. Missing Type Definitions

### Issue
Several types are used but not defined:

- `hash256_t` - Used in streaming_dag.h and hierarchical_vrf.h but not defined
- `circular_proof_t` - streaming_dag.h includes circular_recursion.h but uses wrong type
- Various config structs (`trigger_config_t`, `dag_config_t`, `vrf_tree_config_t`)

### Fix Required
- Add missing type definitions
- Ensure all headers include their dependencies

## 3. Non-existent Functions Called

### In optimized_consensus_engine.c:
- `trigger_engine_should_trigger` (line 29) - doesn't exist
- `trigger_engine_create` (line 244) - doesn't exist  
- `trigger_engine_destroy` (line 303) - doesn't exist
- `vrf_tree_get_root_proof` (line 50, 110) - doesn't exist
- `streaming_dag_create` (line 255) - doesn't exist
- `vrf_tree_create` with config (line 265) - signature mismatch
- `streaming_dag_start_round` (line 140) - doesn't exist
- `streaming_dag_finalize_round` (line 147) - doesn't exist

### In streaming_dag_impl.c:
- `basefold_raa_circular_prove` (line 170) - should be from circular_recursion.h
- `basefold_raa_verify` called with 1 arg (line 386) - needs 2 args

## 4. Incomplete Implementations

### streaming_dag_impl.c:
- Line 176: `vertex = NULL; /* In production, would follow chain */` - chain following not implemented
- Line 246: Missing proper chain implementation for vertex hash map
- Simplified signature verification (line 84)

### early_finality.c:
- Line 376: `/* In production, would collect actual signatures */` - signature collection stubbed
- Line 456: Slashing detection returns NULL - not implemented

### parallel_proof_pipeline.c:
- Line 131-204: Stage functions use `usleep` to simulate work - need actual implementations
- Line 202: Comment says "would call basefold_raa_prove() here" but doesn't

## 5. Configuration Structure Issues

### Missing struct definitions:
- `trigger_config_t` (optimized_consensus_engine.c:240)
- `dag_config_t` (optimized_consensus_engine.c:249)  
- `vrf_tree_config_t` (optimized_consensus_engine.c:259)
- `blockchain_t` (multiple files)

## 6. Function Signature Mismatches

### vrf_tree_create:
- Declaration: `vrf_tree_create(uint32_t validator_count)`
- Usage: `vrf_tree_create(&vrf_cfg)` with config struct

### cmptr_pos_compute_vrf:
- Used in optimized_consensus_engine.c:114 but not defined in headers

## 7. Mock/Stub Implementations

### optimized_consensus_benchmark (line 495):
- Uses `usleep(600000)` to simulate baseline - not actual benchmark
- Creates mock accumulator/blockchain (lines 508-509)

## 8. Missing Error Handling

- Many functions don't check return values
- Memory allocation failures not always handled
- No cleanup on partial initialization failures

## 9. Thread Safety Issues

- Some shared data accessed without proper locking
- Race conditions possible in pipeline worker threads

## 10. Missing Dependencies

### Include files not checking dependencies:
- `streaming_dag.h` uses `hash256_t` without defining/including it
- `hierarchical_vrf.h` same issue
- Missing includes for pthread types in some headers

## Recommendations

1. **Fix API calls**: Update all basefold_raa function calls to match actual API
2. **Add missing types**: Create a common types header with hash256_t, etc.
3. **Implement stubs**: Replace TODO comments with actual implementations
4. **Fix signatures**: Ensure all function declarations match their usage
5. **Add error handling**: Comprehensive error checking and cleanup
6. **Create config headers**: Define all config structures properly
7. **Fix thread safety**: Add proper synchronization where needed
8. **Complete benchmarks**: Replace sleep-based simulations with real benchmarks
9. **Add unit tests**: Test each component in isolation
10. **Documentation**: Add inline docs explaining the optimizations

## Priority Issues (Must Fix)

1. basefold_raa API mismatches - code won't compile
2. Missing type definitions - compilation errors
3. Non-existent function calls - linker errors
4. Configuration struct definitions - needed for compilation

## Files Needing Most Work

1. `streaming_dag_impl.c` - Wrong API usage, incomplete chain implementation
2. `optimized_consensus_engine.c` - Many non-existent functions called
3. `hierarchical_vrf.c` - API mismatches with basefold_raa
4. `early_finality.c` - Stub implementations, API mismatches