# Gate Computer Testing Guide

## 🧪 Comprehensive Testing Framework

Gate Computer includes a professional testing framework with coverage reporting, benchmarking, and CI/CD integration.

## Quick Start

```bash
# Build with tests
mkdir build && cd build
cmake .. -DBUILD_TESTING=ON
make -j$(nproc)

# Run all tests
ctest --output-on-failure

# Run comprehensive test suite
./tests/comprehensive/run_comprehensive_tests

# Run with verbose output
./tests/comprehensive/run_comprehensive_tests --verbose

# Run benchmarks
./tests/comprehensive/run_comprehensive_tests --benchmark
```

## Test Categories

### 1. Unit Tests
- **Framework**: Custom lightweight framework in `tests/framework/`
- **Coverage**: Individual functions and modules
- **Location**: `tests/unit/`

### 2. Comprehensive Tests
- **BaseFold RAA**: Complete proof system testing
- **WebView**: Cross-platform UI testing
- **GF128**: Field arithmetic verification
- **Security**: Cryptographic property validation
- **Location**: `tests/comprehensive/`

### 3. Integration Tests
- **SHA3 Proofs**: End-to-end proof generation
- **Performance**: Timing and throughput
- **Location**: `tests/integration/`

### 4. Security Tests
- **Randomness**: Statistical quality tests
- **Zero-Knowledge**: Privacy verification
- **Constant-Time**: Side-channel resistance
- **Location**: `tests/security/`

## Test Framework Features

### Assertions
```c
ASSERT_TRUE(condition);
ASSERT_FALSE(condition);
ASSERT_EQ(expected, actual);
ASSERT_NE(expected, actual);
ASSERT_STR_EQ(expected, actual);
ASSERT_PTR_NULL(ptr);
ASSERT_PTR_NOT_NULL(ptr);
ASSERT_MEM_EQ(expected, actual, size);
```

### Test Structure
```c
// Define test case
TEST_CASE(suite_name, test_name) {
    // Setup
    void* data = setup_test_data();
    
    // Test
    ASSERT_TRUE(perform_operation(data));
    
    // Cleanup
    cleanup_test_data(data);
    
    return TEST_PASS;
}

// Define test suite
TEST_SUITE(suite_name) {
    test_suite_t* suite = test_create_suite("Suite Name", 
        "Suite description");
    
    // Register test cases
    register_test_suite_name_test_name(suite);
    
    return suite;
}
```

### Benchmarking
```c
TEST_CASE(suite, benchmark_operation) {
    if (!g_benchmark_mode) {
        return TEST_SKIP;
    }
    
    BENCHMARK("operation_name", 1000) {
        perform_operation();
    }
    
    return TEST_PASS;
}
```

## Coverage Analysis

```bash
# Build with coverage
cmake .. -DCMAKE_BUILD_TYPE=Coverage
make

# Run tests
ctest

# Generate HTML report
lcov --capture --directory . --output-file coverage.info
genhtml coverage.info --output-directory coverage_html

# View report
firefox coverage_html/index.html
```

## CI/CD Integration

The project includes GitHub Actions workflows for:
- Multi-platform builds (Linux, macOS)
- Multiple compilers (GCC, Clang)
- Coverage reporting with Codecov
- Static analysis (cppcheck, clang-tidy)
- Benchmark tracking

## Performance Testing

### Proof Generation Benchmarks
```bash
# Run performance tests
./tests/comprehensive/run_comprehensive_tests --benchmark

# Expected results:
# - Proof generation: ~150ms (SHA3-256)
# - Verification: ~8ms
# - GF128 multiplication: ~2ns per operation
```

### Memory Testing
```bash
# Run with valgrind
valgrind --leak-check=full ./tests/comprehensive/run_comprehensive_tests

# Run with address sanitizer
cmake .. -DCMAKE_C_FLAGS="-fsanitize=address"
make
./tests/comprehensive/run_comprehensive_tests
```

## Test Reports

### XML Report (JUnit format)
```bash
./tests/comprehensive/run_comprehensive_tests --xml results.xml
```

### JSON Report
```bash
./tests/comprehensive/run_comprehensive_tests --json results.json
```

### Coverage Report
```bash
./tests/comprehensive/run_comprehensive_tests --coverage-report coverage.html
```

## Writing New Tests

1. Create test file in appropriate directory
2. Include test framework header
3. Write test cases using TEST_CASE macro
4. Create test suite using TEST_SUITE macro
5. Add to CMakeLists.txt
6. Run and verify

### Example Test
```c
#include "../framework/test_framework.h"
#include "my_module.h"

TEST_CASE(my_module, basic_functionality) {
    // Arrange
    my_data_t* data = my_module_create();
    ASSERT_PTR_NOT_NULL(data);
    
    // Act
    int result = my_module_process(data, 42);
    
    // Assert
    ASSERT_EQ(0, result);
    ASSERT_EQ(42, data->value);
    
    // Cleanup
    my_module_destroy(data);
    
    return TEST_PASS;
}

TEST_SUITE(my_module) {
    test_suite_t* suite = test_create_suite("My Module", 
        "Tests for my module functionality");
    
    register_test_my_module_basic_functionality(suite);
    
    return suite;
}
```

## Test Coverage Goals

- **Overall**: > 80% line coverage
- **Critical paths**: > 95% coverage
- **Security code**: 100% coverage
- **Error handling**: 100% coverage

## Troubleshooting

### Test Failures
1. Run with `--verbose` for detailed output
2. Check test logs in `build/Testing/Temporary/`
3. Use debugger: `gdb ./test_name`

### Coverage Issues
1. Ensure `-DCMAKE_BUILD_TYPE=Coverage`
2. Check for inline functions (may not be counted)
3. Verify gcov/lcov versions match compiler

### Performance Variations
1. Disable CPU frequency scaling
2. Run on isolated CPU cores
3. Use `--benchmark` mode for accurate timing

## Best Practices

1. **Fast Tests**: Keep unit tests under 100ms
2. **Independent**: Tests should not depend on each other
3. **Repeatable**: Same result every time
4. **Clear Names**: Describe what is being tested
5. **One Assertion**: Test one thing per test case
6. **Clean State**: Always cleanup resources

## Testing Truth Statements

The testing framework verifies Truth Bucket statements:

```bash
# Verify all testing-related truths
./build/bin/verify_truths --category 4  # Testing category

# Current testing truths verified:
# - T301: Unit test framework exists ✓
# - T302: Integration tests cover all modules ✓
# - T303: Performance benchmarks automated ✓
# - T304: Security tests for all crypto operations ✓
```