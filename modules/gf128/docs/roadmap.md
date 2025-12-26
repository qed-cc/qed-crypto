 # GF128 Arithmetic Library

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
 ├── docs/roadmap.md       # Project documentation and roadmap
 ├── include/
 │   └── gf128.h           # Public API
 ├── src/
 │   ├── gf128_base.c      # Reference implementations
 │   ├── gf128_table.c     # Table-driven implementation
 │   ├── gf128_pclmul.c    # PCLMUL intrinsics implementation
 │   ├── gf128_inv.c       # Inversion/division routines
 │   └── gf128_dispatch.c  # Generic multiply dispatch
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
 mkdir build && cd build
 cmake -DCMAKE_BUILD_TYPE=Release ..
 cmake --build .
 ctest --timeout 100
 ```

 ## Benchmarking
 ```sh
 # After building:
 ./benchmarks/bench_mul
 ```
 Benchmarks will report throughput (cycles/byte) for each multiplication implementation.

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