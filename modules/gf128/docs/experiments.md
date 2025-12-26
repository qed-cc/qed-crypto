<!-- docs/experiments.md -->
# Performance Experimentation Guide

This document describes how to reproduce and analyze performance experiments for GF(2^128) multiplication variants.

## 1. Hardware & Environment Setup
- Use a dedicated benchmarking machine or ensure minimal background load.
- Set CPU governor to performance mode:
  ```sh
  sudo cpupower frequency-set --governor performance
  ```
- Pin benchmark process to isolated cores (e.g., core 4):
  ```sh
  taskset --cpu-list 4 ./benchmarks/bench_mul
  ```

## 2. Running Experiments

For each compile-time variant, rebuild and run the C benchmark executable with CSV output.

Example for AVX2 + AVX-512 + Karatsuba variant (if enabled):
```sh
mkdir build && cd build
cmake -DCMAKE_BUILD_TYPE=Release \
      -DUSE_AVX2=ON -DUSE_AVX512=ON -DUSE_PCLMUL_KARATSUBA=ON ..
cmake --build . --target bench_mul
../benchmarks/bench_mul --csv > ../results_avx2_avx512_kara.csv
```

## 3. Data Analysis

- Load the CSV output file (e.g., `results.csv`) into your favorite analysis tool (Excel, Python, R).
- For statistical rigor, repeat the benchmark multiple times and aggregate the `Mops` values manually.
- Compute mean, standard deviation, and plot comparisons (bar charts, heatmaps) annotated with hardware and CMake flags.

## 4. Extending Experiments

To add a new compile-time variant (e.g., `-DUSE_SLICEBY8=ON`):
1. Add the CMake option and guard in `CMakeLists.txt` and source files.
2. Rebuild `bench_mul` with the new flag.
3. Run `bench_mul --csv` to collect performance data.

---
Maintainers should commit raw benchmark CSV outputs (e.g., `results.csv`) and any plots or analysis files under `docs/experiments/` for future reference.