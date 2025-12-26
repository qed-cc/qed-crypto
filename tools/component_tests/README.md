# BaseFold Verifier Circuit Component Test Suite

## Overview

This test suite provides comprehensive testing for the BaseFold verifier circuit components. Each component is tested independently to ensure correctness before integration.

## Components Tested

### 1. GF(2^128) Arithmetic (`test_gf128`)
- **Addition**: XOR operation correctness
- **Multiplication**: Proper reduction with polynomial x^128 + x^7 + x^2 + x + 1
- **Circuit Generation**: Gate count and structure verification
- **Circuit Simulation**: Basic operation verification

### 2. SHA3-256 Hashing (`test_sha3`)
- **NIST Test Vectors**: Known input/output pairs
- **Various Input Sizes**: Edge cases and buffer boundaries
- **Keccak Permutation**: Basic property checks
- **Incremental Hashing**: Streaming API consistency
- **Performance**: Throughput benchmarks

### 3. Merkle Trees (`test_merkle`)
- **4-ary Tree Construction**: Proper tree building
- **Path Verification**: Authentication path correctness
- **Edge Cases**: Non-power-of-4 leaf counts
- **Circuit Generation**: Verification circuit structure
- **Performance**: Tree construction speed

### 4. Sumcheck Protocol (`test_sumcheck`)
- **Round Verification**: g(0) + g(1) = claimed_sum
- **Multiple Rounds**: Protocol simulation
- **Edge Cases**: Zero/constant polynomials
- **Circuit Generation**: Round verification circuit
- **Performance**: Polynomial evaluation speed

### 5. FRI Protocol (`test_fri`)
- **Folding Operation**: Correct polynomial folding
- **Query Generation**: Deterministic query indices
- **Round Consistency**: Multi-round verification
- **Final Polynomial**: Evaluation correctness
- **Performance**: Folding throughput

## Building and Running

### Prerequisites
```bash
# Build the main project first
cd ../..
mkdir -p build && cd build
cmake .. && make
```

### Run All Tests
```bash
cd tools/component_tests
./run_tests.sh
```

### Run Individual Tests
```bash
make test-gf128    # Test GF(2^128) arithmetic
make test-sha3     # Test SHA3-256
make test-merkle   # Test Merkle trees
make test-sumcheck # Test sumcheck protocol
make test-fri      # Test FRI protocol
```

### Clean Build
```bash
make clean
make all
```

## Test Output

Each test suite reports:
- Individual test results (PASSED/FAILED)
- Performance metrics where applicable
- Summary statistics

Example output:
```
Running GF128 Component Tests...

  Testing GF128 Addition... PASSED (0.001s)
  Testing GF128 Multiplication... PASSED (0.002s)
  Testing GF128 Circuit Generation... 
    Generated circuit with 33152 gates PASSED (0.015s)
  Testing GF128 Circuit Simulation... PASSED (0.001s)

GF128 Test Summary:
  Passed: 4
  Failed: 0
  Total:  4
  Status: SUCCESS
```

## Circuit Files Generated

The tests generate several circuit files for inspection:
- `test_gf128_ops.circuit` - GF128 addition and multiplication
- `test_gf128_simple.circuit` - Simple GF128 addition
- `test_sha3_simple.circuit` - Simplified SHA3 circuit
- `test_merkle_verify.circuit` - Merkle path verification
- `test_sumcheck_round.circuit` - Single sumcheck round
- `test_fri_folding.circuit` - FRI folding verification

## Performance Targets

- GF128 operations: >100k ops/second
- SHA3-256: >1 MB/s throughput
- Merkle tree: >200 leaves/second
- Sumcheck: >100k polynomial evaluations/second
- FRI folding: <2s for 4 rounds on 2^16 domain

## Debugging Failed Tests

If a test fails:

1. **Check error messages** - Tests provide detailed failure reasons
2. **Examine generated circuits** - Look for structural issues
3. **Run with gdb** - `gdb ./test_component` for detailed debugging
4. **Check library versions** - Ensure GF128 and SHA3 libraries are current

## Adding New Tests

To add a new test:

1. Create `test_component.c` following the pattern of existing tests
2. Include `test_framework.h` for utilities
3. Add to `TESTS` variable in Makefile
4. Use `TEST_START`, `TEST_ASSERT`, `TEST_END` macros
5. Run `make test-component` to test individually

## Known Issues

1. **Large circuits** - Full verifier circuit too large for simulation
2. **Memory usage** - Some tests allocate significant memory
3. **Platform differences** - Timing may vary across systems

## Future Improvements

1. **Property-based testing** - Random input generation
2. **Formal verification** - Integration with SAT/SMT solvers
3. **Coverage analysis** - Ensure all code paths tested
4. **Differential testing** - Compare against reference implementations
5. **Fuzzing** - Find edge cases automatically