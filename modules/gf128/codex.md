<!-- LLM Developer Guide: This file provides AI agents with project context and roadmap instructions. -->

# GF128 Arithmetic Library

## One-Line Quick Benchmark

From a fresh clone, just run:

```bash
git clone https://github.com/RhettCreighton/gf128.git \
  && cd gf128 \
  && bash bench.sh
```

This builds all optimized variants (bitwise, table-driven, PCLMUL, AVX2, AVX-512, GFNI) and immediately prints:
- Single-threaded throughput (sorted by best performer)
- Full core-count (nproc) multi-threaded throughput

No extra flags required — you’ll see the fastest GF(2^128) path on your machine right away.

### Example Output
On a 16-core AVX-512/GFNI-capable machine, running `bash bench.sh` produces:
```
==> Single-threaded GF(2^128) multiply throughput (Mops/sec)
gf128_mul8_pclmul_avx512_super      1624.68
gf128_mul4_pclmul_avx512            1450.84
gf128_mul2_pclmul_avx2               380.59
gf128_mul_pclmul_avx2                 91.55
gf128_mul_pclmul_avx512               77.63
gf128_mul_pclmul_kara                 62.87
gf128_mul_pclmul                       4.16
gf128_mul_table                        4.11
gf128_mul                              3.97
gf128_mul_base                         3.28

==> Multi-threaded GF(2^128) multiply throughput (all 16 cores, Mops/sec)
gf128_mul8_pclmul_avx512_super      9626.94
gf128_mul4_pclmul_avx512            1426.01
gf128_mul2_pclmul_avx2               380.23
gf128_mul_pclmul_avx2                 91.51
gf128_mul_pclmul_avx512               76.36
gf128_mul_pclmul_kara                 62.51
gf128_mul                              4.01
gf128_mul_table                        3.99
gf128_mul_pclmul                       3.94
gf128_mul_base                         3.24
```

## Cleaning Up Old Builds

If you have leftover out-of-source build directories (e.g., `build/`, `build_gfni/`, `build_opt/`), you can remove them all at once:
```sh
rm -rf build*/
```
This cleans the workspace so you always start from a fresh build.


## Overview
This project provides optimized finite field GF(2^128) arithmetic routines in C (C99). Primary focus: high-performance multiplication, addition, and inversion.

## Goals
- Implement multiple multiplication algorithms:
  - Naive bitwise implementation
  - Table-driven implementation
  - Carry-less multiplication using PCLMUL intrinsics
- Benchmark and compare implementations
- Provide a clean CMake-based build system
- Include unit tests and benchmarks
- Deliver well-documented API and design rationale

## Directory Structure
```
.
├── CMakeLists.txt        # Top-level CMake build script
├── .gitignore
├── codex.md              # Project documentation and roadmap
├── include/
│   └── gf128.h           # Public API
├── src/
│   ├── gf128_base.c      # Reference implementations
│   ├── gf128_table.c     # Table-driven implementation
│   └── gf128_pclmul.c    # PCLMUL intrinsics implementation
├── tests/
│   ├── CMakeLists.txt    # Unit tests build script
│   └── test_gf128.c      # Unit tests using CTest
├── benchmarks/
│   ├── CMakeLists.txt    # Benchmarks build script
│   └── bench_mul.c       # Benchmark harness
├── examples/
│   └── example.c         # Usage examples
└── docs/
    └── design.md         # Deep dive into algorithm choices
```

## Build & Test
```sh
# Basic build & test (default variants)
mkdir build && cd build
cmake -DCMAKE_BUILD_TYPE=Release ..
cmake --build .
ctest --timeout 100
```

To verify correctness of all optimized multiply variants (Karatsuba, AVX2, AVX-512, GFNI, GFNI-only), build and run the dedicated test target:

```sh
rm -rf build && mkdir build && cd build
cmake -DCMAKE_BUILD_TYPE=Release \
      -DUSE_PCLMUL=ON \
      -DUSE_PCLMUL_KARATSUBA=ON \
      -DUSE_AVX2=ON \
      -DUSE_AVX512=ON \
      -DUSE_GFNI=ON \
      -DUSE_GFNI_MUL=ON \
      ..
cmake --build . --target test_gf128
ctest --output-on-failure
```

## Benchmarking

First, build the benchmark target:

```sh
mkdir -p build && cd build
cmake -DCMAKE_BUILD_TYPE=Release \
      -DUSE_AVX2=ON \
      -DUSE_AVX512=ON \
      -DUSE_GFNI=ON \
      -DENABLE_MICROTUNE=ON ..
cmake --build . --target bench_mul
```

Then run:

- Single-threaded (all variants):
  ```sh
  ./benchmarks/bench_mul
  ```
- CSV output (single-threaded):
  ```sh
  ./benchmarks/bench_mul --csv > results.csv
  ```
- Multi-threaded super-batch (8-way) across N threads:
  ```sh
  ./benchmarks/bench_mul --threads N [--csv]
  ```
  This spawns N pthreads, each executing the 8-way super-batch path. The reported Mops/sec is the aggregate across all threads.

Example: find the top performer on all cores:

```sh
./benchmarks/bench_mul --threads $(nproc) --csv \
  | sort -t, -k2 -nr \
  | head -n1
```

Sample CSV output:

```txt
method,Mops
gf128_mul8_pclmul_avx512_super,1764.37
gf128_mul4_pclmul_avx512,1696.35
gf128_mul2_pclmul_avx2,386.44
...
```

Notes:
- Only the 8-way AVX-512 “super-batch” path is parallelized by `--threads`.
- Other variants (4-way, 2-way, scalar) run single-threaded.
  
## Integration with CMake Projects

This library exports a CMake package for easy consumption by other CMake-based C99 projects. After installing (via `make install`), link against the `gf128::gf128` target:

```cmake
find_package(gf128 0.1.0 REQUIRED)
add_executable(myapp main.c)
target_link_libraries(myapp PRIVATE gf128::gf128)
```

The `gf128::gf128` target automatically sets include directories and compile definitions.

Control performance variants at configure time by passing CMake options:
```sh
-DUSE_PCLMUL=ON           # enable carry-less PCLMUL intrinsics (default ON)
-DUSE_PCLMUL_KARATSUBA=ON # enable Karatsuba optimization (3 CLMULs)
-DUSE_AVX2=ON             # enable AVX2 2-way batched PCLMUL
-DUSE_AVX512=ON           # enable AVX-512 4-way/8-way batched PCLMUL
-DUSE_GFNI=ON             # enable GFNI-accelerated reduction
-DENABLE_MICROTUNE=ON     # enable -Ofast -march=native -flto tuning
```

Use `gf128_mul(a, b)` for automatic runtime dispatch, or call specific variants (`gf128_mul_table`, `gf128_mul_pclmul`, etc.). Hardware support checks:
```c
if (gf128_has_avx2()) { /* AVX2+PCLMUL supported */ }
if (gf128_has_avx512()) { /* AVX-512 supported */ }
if (gf128_has_gfni()) { /* GFNI supported */ }
```
  
## Contributing
- Follow C99 and project coding style
- Write unit tests for new features
- Benchmark performance changes
- Use descriptive commit messages

## Roadmap
- [x] Reference bitwise multiplication implementation
- [x] Table-driven multiplication implementation (src/gf128_table.c)
- [x] PCLMUL-based multiplication implementation (src/gf128_pclmul.c)
- [x] Inversion and division routines
- [x] Extended unit test suite (randomized vectors, edge cases)
- [x] Benchmark comparisons: reference vs table vs PCLMUL
- [ ] Performance tuning and cache optimizations
- [x] API documentation and usage examples
- [x] Continuous integration (CI) setup
- [ ] Packaging and distribution

Feel free to adjust this plan and propose additional improvements.
## Next Steps & Checklist

- [x] Implement table-driven multiplication and write comprehensive tests
- [x] Implement PCLMUL-based multiplication and write comprehensive tests
- [x] Add inversion and division routines to API and implementation
- [x] Expand unit test suite with randomized vectors and property-based tests
- [x] Add benchmark targets for table-driven and PCLMUL implementations
- [x] Integrate continuous integration (e.g., GitHub Actions) for build, test, and benchmarks
- [ ] Clean up codebase: remove TODOs, enforce coding style, run pre-commit hooks
- [x] Update documentation in docs/design.md with detailed algorithm rationale
 - [ ] Prepare and tag release version 0.1.0, update CHANGELOG or release notes
  
### Performance Optimization Roadmap
Focus first on leveraging GFNI for full-field multiplies, then broaden to other hyper-optimizations:
- [ ] Design & implement pure GFNI multiply kernel
  - Research VGF2P8MULB and VGF2P8AFFINEQB to implement 128×128 GF(2) multiplication entirely with GFNI
  - Create `src/gf128_gfni.c` with `gf128_mul_gfni(gf128_t a, gf128_t b)`
  - Expose CMake option `USE_GFNI_MUL` (OFF by default)
  - Add runtime detection `gf128_has_gfni()` and guard in `gf128_mul` dispatch
  - Write unit tests and update benchmarks to include GFNI path
- [ ] Benchmark GFNI-only path vs. PCLMUL and table-driven variants
- [ ] Document GFNI path in `docs/design.md` and update README
  
#### Subsequent Hyper-Optimization Tasks
- [ ] Implement GFNI-Karatsuba variant to reduce instruction count
- [ ] Explore deeper GFNI batching (e.g., 16-way interleaved super-batch)
- [ ] Hand-tune inline assembly for GFNI kernels for optimal scheduling
- [ ] Inline GFNI hot path and eliminate per-call branches (always_inline, dispatch table)
- [ ] Profile GFNI and PCLMUL variants with perf/VTune; tune prefetch and alignment hints
  
## Performance Experimentation Methodology

To systematically explore and validate optimizations across different platforms, we adopt a scientific approach comprising hypothesis-driven experiments, controlled measurements, and statistical analysis. Future maintainers (including LLM-driven workflows) should follow this framework to ensure reproducibility and rigor.

1. Define Objectives and Hypotheses
   - Identify target metrics (e.g., operations per second, latency, energy consumption).
   - Formulate clear hypotheses (for example: “AVX-512 batched CLMUL will yield ≥3× throughput vs. scalar PCLMUL on Xeon Cascade Lake”).
   - Specify independent variables (instruction set, batch size, data alignment) and dependent variables (throughput, variance).

2. Experimental Infrastructure
   - CMake Feature Flags: add options `-DUSE_AVX2=ON`, `-DUSE_AVX512=ON`, `-DGF128_BATCH_LANES=N` to enable variants.
   - Enhanced Benchmark Harness:
     * Parameterize `bench_mul` to accept variant name, batch size, and trial count.
     * Emit structured output (CSV or JSON) with fields: timestamp, CPU model, compiler flags, variant, batch_size, mean, stddev.
   - Rebuild & Run Workflow:
     * For each desired variant (e.g., default, AVX2, AVX512, Karatsuba, any combination), reconfigure with CMake flags (`-DUSE_AVX2=ON`, `-DUSE_AVX512=ON`, `-DUSE_PCLMUL_KARATSUBA=ON`), then build `bench_mul` and run:
       ```sh
       cmake -DCMAKE_BUILD_TYPE=Release \
         -DUSE_AVX2=ON -DUSE_AVX512=ON -DUSE_PCLMUL_KARATSUBA=ON ..
       cmake --build . --target bench_mul
       ./benchmarks/bench_mul --csv > results_avx512_kara_avx2.csv
       ```

3. Controlled Measurement Protocol
   - Enforce fixed CPU frequency (performance governor) and isolate cores (taskset).
   - Warm-up phase (e.g., 5% of total iterations) to stabilize caches/pipelines.
   - Repeat each configuration ≥10 trials to gather representative samples.

4. Data Analysis and Validation
   - Compute descriptive statistics: mean, standard deviation, confidence intervals.
   - Conduct significance tests (e.g., t-test) for pairwise comparisons.
   - Generate visual reports (bar charts, heatmaps) annotated with hardware capabilities.

5. Iteration and Documentation
   - Accept or reject hypotheses based on statistical evidence.
   - Update implementations (unrolling factors, reduction pipelines, vector widths).
   - Record experiment metadata and conclusions in `docs/experiments.md`.

6. Reproducibility and CI Integration
   - Store configuration files and raw CSV logs in version control.
   - Optionally run a minimal baseline benchmark set in CI to catch regressions.
   - Document hardware/environment setup in `docs/experiments.md`.

### Experiment Checklist
   - [ ] Define hypothesis and target metrics.
   - [ ] Enable desired CMake feature flags.
   - [ ] Configure CPU environment (governor, affinity).
   - [ ] For each variant, rebuild `bench_mul` with appropriate flags and run with `--csv`.
   - [ ] Aggregate CSV outputs externally to compute statistics and visualize results.
   - [ ] Visualize and interpret results.
   - [ ] Decide on next implementation changes or new hypotheses.
   - [ ] Document findings in `docs/experiments.md`.

## AVX2 and AVX-512 Hyper-Optimization Plan

To achieve hyper-optimized GF(2^128) multiplication across modern x86 platforms, we define a multi-tiered roadmap:

### 1. Scalar Karatsuba PCLMUL (3 CLMULs)
  - Implement `gf128_mul_pclmul_kara` in `src/gf128_pclmul_kara.c`, using 3 carry-less multiplies (d0, d2, d1).
  - Enable via CMake option `USE_PCLMUL_KARATSUBA`.

### 2. AVX2 Two-Way Batched CLMUL
  - In `src/gf128_pclmul_avx2.c`, implement `gf128_mul2_pclmul_avx2` that packs two 128-bit pairs into YMM registers,
    issues two parallel PCLMULs on XMM lanes, and applies vectorized reduction.
  - Provide scalar wrapper `gf128_mul_pclmul_avx2` for single-block multiplies.
  - Toggle via CMake option `USE_AVX2` (compile with `-mavx2 -mpclmul`).

### 3. AVX-512 Four-Way Batched CLMUL
  - Complete `gf128_mul4_pclmul_avx512` in `src/gf128_pclmul_avx512.c` using VPCLMULQDQ
    across four 128-bit lanes in ZMM registers and vectorized reduction.
  - Provide scalar wrapper `gf128_mul_pclmul_avx512` by broadcasting inputs to four lanes.
  - Toggle via CMake option `USE_AVX512` (compile with `-mavx512f -mavx512bw -mavx512vl -mavx512dq -mpclmul`).

### 4. Dispatch and Runtime Selection
  - Update `src/gf128_dispatch.c` to prefer variants in order: AVX-512 > AVX2 > Karatsuba > PCLMUL > table.
  - Add runtime feature checks `gf128_has_avx2()` and `gf128_has_avx512()` in `include/gf128.h`.

### 5. CMake & Build Integration
  - Expose CMake options: `USE_PCLMUL_KARATSUBA`, `USE_AVX2`, `USE_AVX512` (all OFF by default).
  - Under each option, apply the appropriate compiler flags and link the corresponding sources.

### 6. Benchmarking & Validation
  - Extend `benchmarks/bench_mul.c` to accept a `--variant` flag (`base`, `table`, `pclmul`, `kara`, `avx2`, `avx512`).
  - Report per-variant throughput (lanes × Mops/sec) and aggregate performance.
  - Add unit tests for `gf128_mul2_pclmul_avx2` and `gf128_mul4_pclmul_avx512`, verifying each lane
    against the reference `gf128_mul_base`.

### Metrics & Success Criteria
  - Karatsuba scalar: ≥15% speed-up vs. 4-CLMUL scalar.
  - AVX2 2-way batch: ≥2× aggregate throughput vs. Karatsuba scalar.
  - AVX-512 4-way batch: ≥4× aggregate throughput vs. Karatsuba scalar.
  - All implementations must pass existing and new bitwise-correctness tests (100% accuracy).

Maintain this plan in `codex.md` as the authoritative roadmap for hyper-optimization.
## World-Record Breaking Hyper-Optimization Checklist

To push GF(2^128) multiplication performance in this library to unprecedented levels, we will systematically tackle the following tasks. Each item must be correct (bitwise-equivalent to the reference) and validated by unit tests and benchmarks.

- [x] Complete and optimize AVX-512 reduction logic
-    - Fully implement `gf128_reduce_avx512` using `_mm512_clmulepi64_epi128` and `_mm512_alignr_epi8`
-    - Removed scalar fallbacks; all lanes reduced in parallel

- [x] Implement and benchmark AVX-512 4-way PCLMUL variant
    - Added `gf128_mul4_pclmul_avx512` and `bench4` harness in `bench_mul.c`
    - Achieved ~1.04 Gops/sec aggregate (~260 Mops/sec per lane) on Zen4
- [ ] Benchmark and validate AVX-512 Karatsuba path end-to-end
    - Enable `USE_AVX512` in CMake, build bench targets, and collect CSV/JSON results
    - Compare against scalar and AVX2 variants for speedups
- [ ] Explore deeper AVX2 multi-lane interleaving
    - 2-way batched PCLMUL already in place; 4-way across YMM not available on AVX2
    - Consider manual interleaving of 4 scalar CLMULs to fill pipelines
- [x] Micro-optimize inner loops and data paths
    - Used `_mm_alignr_epi8`/`_mm512_alignr_epi8` to replace shuffles in reduction
    - Next: add `__restrict` and alignment hints to boost memory throughput
    - Investigate inline assembly stubs for latency-critical sequences
- [ ] Improve runtime dispatch and inlining
    - Build a dispatch table of function pointers at init to eliminate per-call branches
    - Use `__attribute__((always_inline))` on hot scalar wrappers
- [ ] Profile on target CPUs (Intel, AMD)
    - Use `perf` or `vtune` to locate hotspots and instruction-level stalls
    - Tune based on actual microarchitecture behaviors (e.g., port pressure)
- [ ] Expand unit tests and property-based tests
    - Add randomized test vectors for each new variant (Karatsuba, AVX2, AVX512)
    - Ensure 100% bitwise correctness against `gf128_mul_base`
- [ ] Automate performance regression tracking in CI
    - Integrate benchmark runs in GitHub Actions or similar, recording Mops/sec over time
    - Fail builds on significant regressions
 - [ ] Investigate alternative platforms and accelerators
    - Explore ARM NEON/PMULL implementations for cross-platform performance
    - Prototype GPU-based GF(2^128) batch multiplies (CUDA/OpenCL)
    - Compare against CPU variants for throughput per watt

## +20% World-Record Mission Checklist
To achieve a ≥20% speedup above the current AVX-512 record (~1.07 Gops/sec), we will tackle these high-impact optimizations. Each item must be validated for correctness and performance.
- [ ] Implement AVX-512 Karatsuba PCLMUL path
- [ ] Integrate GFNI-based reduction (use VGF2P8MULB / VGF2P8AFFINEQB) for both partial products and final reduction
- [ ] Enable architecture-specific tuning: compile with `-march=native`, `-Ofast`, and `-flto` for hot kernels
- [ ] Annotate and inline AVX-512 kernels: use `__attribute__((always_inline,target("avx512f,pclmul")))`
- [ ] Unroll & pipeline multiplies: interleave two 4-way batches into an 8-way “super-batch” to hide VPCLMULQDQ latency
- [ ] Optimize bench harness:
  - Remove `% N_PAIRS` in loop indices; switch to simple pointer wrap-around
  - Add `_mm_prefetch` hints for input arrays to ensure L1 residency
- [ ] Extend bench_mul to support multi-threaded runs, measuring aggregate throughput per core
  
Once this checklist is complete and all items validated, we should surpass 1.3 Gops/sec on AVX-512 hardware. Future AI-driven workflows can reference this section to guide implementation and benchmarking.
