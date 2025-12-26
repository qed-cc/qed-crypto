# Semantic Q&A System Guide

## Overview

The gate_computer now includes an AI semantic meaning functionality that can answer questions about the library's performance by running actual benchmarks and recording results with detailed hardware specifications.

## Key Features

- **Natural Language Understanding**: Maps questions to executable benchmark tests
- **Automatic Benchmarking**: Runs real code to get accurate performance data
- **Hardware Detection**: Records CPU, memory, OS, compiler, and SIMD capabilities
- **Historical Database**: Saves all results for future comparisons
- **Extensible Framework**: Easy to add new questions and benchmarks

## Usage

### Basic Usage

```bash
# List available questions
./tools/semantic_qa_simple

# Ask a specific question (by number)
./tools/semantic_qa_simple 1
```

### Example Session

```bash
$ ./tools/semantic_qa_simple 1

🤖 Gate Computer Semantic Q&A System
Initializing benchmark system...

⏳ Running benchmark for: How long does this library take to prove a bitcoin block?

========== Benchmark Result ==========
Question: How long does this library take to prove a bitcoin block?
✅ Answer: It takes 0.850 seconds to generate a zero-knowledge proof for a Bitcoin block 
          with 690,000 gates on AMD Ryzen 7 PRO 8840U with 16 cores.
📊 Measurement: 0.850074 seconds

🖥️  Hardware Specifications:
   CPU: AMD Ryzen 7 PRO 8840U w/ Radeon 780M Graphics
   Cores: 16 (physical) / 16 (logical)
   Memory: 62935 MB
   OS: Linux 6.11.0-26-generic
   Compiler: gcc 13.3.0
   Architecture: x86_64
   Timestamp: 2025-05-27 22:21:10

ℹ️  Additional Information:
   Circuit size: 690K gates, Input: 80-byte Bitcoin header, 
   Proof size: ~65KB, Algorithm: BaseFold

💾 Result saved to benchmark_results.json
```

## Available Questions

1. **How long does this library take to prove a bitcoin block?**
   - Measures time to generate a ZK proof for 690K gate Bitcoin circuit
   - Returns: Time in seconds

2. **What is the gate evaluation throughput?**
   - Measures gates evaluated per second across various circuit sizes
   - Returns: Gates/second

3. **How much memory does a Bitcoin proof require?**
   - Measures peak memory usage during proof generation
   - Returns: Memory in MB

4. **What is the proof size for a Bitcoin block?**
   - Calculates the size of the generated zero-knowledge proof
   - Returns: Size in bytes

5. **How long does SHA3-256 proof generation take?**
   - Measures proof generation time for SHA3-256 (192K gates)
   - Returns: Time in seconds

6. **Can the system handle circuits with 1 million gates?**
   - Tests whether large circuits can be processed
   - Returns: Yes/No with details

7. **What is the verification time for a Bitcoin proof?**
   - Measures time to verify a zero-knowledge proof
   - Returns: Time in seconds

8. **How does performance scale with circuit size?**
   - Analyzes performance across different circuit sizes
   - Returns: Scaling analysis

## Architecture

### Module Structure

```
modules/semantic_qa/
├── include/
│   └── semantic_qa.h         # Core API definitions
├── src/
│   ├── semantic_qa.c         # Q&A engine implementation
│   └── benchmark_tests.c     # Actual benchmark implementations
└── CMakeLists.txt           # Build configuration
```

### Key Components

1. **Hardware Detection** (`hardware_spec_t`)
   - CPU model, cores, frequency
   - Memory capacity
   - OS and compiler information
   - SIMD capabilities (AVX2, AVX512)

2. **Benchmark Results** (`benchmark_result_t`)
   - Question and answer text
   - Numerical measurement and unit
   - Complete hardware specifications
   - Timestamp and success status

3. **Test Registration**
   - Function pointer based system
   - Easy to add new benchmarks
   - Automatic question-to-test mapping

## Adding New Questions

To add a new question:

1. Add question to `PREDEFINED_QUESTIONS` array:
```c
{
    "What is the circuit compilation time?",
    QA_TYPE_PERFORMANCE,
    "benchmark_compilation_time",
    "seconds",
    "Measures time to compile C code to circuit"
}
```

2. Implement the benchmark function:
```c
benchmark_result_t benchmark_compilation_time(void) {
    benchmark_result_t result = {0};
    
    // Detect hardware
    detect_hardware_specs(&result.hardware);
    
    // Run benchmark
    // ... measurement code ...
    
    // Set results
    result.measurement_value = compile_time;
    snprintf(result.answer, sizeof(result.answer),
             "Compilation takes %.3f seconds on %s",
             compile_time, result.hardware.cpu_model);
    
    result.success = true;
    return result;
}
```

3. Register the benchmark:
```c
register_benchmark_test("benchmark_compilation_time", 
                       benchmark_compilation_time,
                       "Measure circuit compilation time");
```

## Database Format

Results are saved in JSON format to `benchmark_results.json`:

```json
{
  "question": "How long does this library take to prove a bitcoin block?",
  "answer": "It takes 0.850 seconds...",
  "measurement_value": 0.850074,
  "measurement_unit": "seconds",
  "timestamp": 1748398870,
  "success": true,
  "test_function": "benchmark_bitcoin_proof_time",
  "hardware": {
    "cpu_model": "AMD Ryzen 7 PRO 8840U",
    "cpu_cores": 16,
    "cpu_threads": 16,
    "cpu_freq_mhz": 5132,
    "ram_total_mb": 62935,
    "os_name": "Linux",
    "os_version": "6.11.0-26-generic",
    "compiler": "gcc 13.3.0",
    "architecture": "x86_64",
    "has_avx2": false,
    "has_avx512": false
  }
}
```

## Future Enhancements

1. **Natural Language Processing**: Better question matching using NLP techniques
2. **Comparative Analysis**: Compare results across different hardware automatically
3. **Visualization**: Generate performance graphs and charts
4. **CI/CD Integration**: Run benchmarks automatically on commits
5. **Web Interface**: REST API for remote benchmarking
6. **Machine Learning**: Predict performance on untested hardware

## Benefits

- **Automated Documentation**: Performance characteristics are self-documenting
- **Hardware Awareness**: Results are always contextualized with hardware specs
- **Reproducibility**: Anyone can run the same benchmarks on their hardware
- **Historical Tracking**: Performance changes over time are tracked
- **Decision Support**: Helps users understand if the library meets their needs