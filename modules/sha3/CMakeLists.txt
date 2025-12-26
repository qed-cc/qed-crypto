# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2025 Rhett Creighton

cmake_minimum_required(VERSION 3.12)
project(sha3 VERSION 1.0.0 LANGUAGES C)
find_package(Threads REQUIRED)

# Set C standard
set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

# Include project headers
include_directories(
    ${CMAKE_CURRENT_SOURCE_DIR}/include
)

# Library source files
set(SHA3_SOURCES
    src/sha3.c
    src/sha3_avx2.c
    src/sha3_avx2_batch.c
    src/sha3_parallel.c
    src/keccak.c
    src/keccak_avx2.c
    src/keccak_avx512.c
    src/shake.c
    src/hash_function.c
    src/merkle.c
)
## Add XKCP KeccakP-1600-times8 AVX512 full-unroll kernel

## Create library (static by default)
add_library(sha3 ${SHA3_SOURCES})
## Link threads for parallel hashing
target_link_libraries(sha3 PUBLIC Threads::Threads)
  # Optional: integrate XKCP KeccakP-1600-times8 AVX512 full-unroll kernel if available
  set(XKCP_TIMES8_DIR ${CMAKE_CURRENT_SOURCE_DIR}/vendor/XKCP/lib/low/KeccakP-1600-times8/AVX512)
  if(EXISTS "${XKCP_TIMES8_DIR}/KeccakP-1600-times8-SIMD512.c")
    message(STATUS "Integrating XKCP AVX512 kernel from ${XKCP_TIMES8_DIR}")
    target_include_directories(sha3 PRIVATE
        ${XKCP_TIMES8_DIR}/ua
        ${XKCP_TIMES8_DIR}
        ${CMAKE_CURRENT_SOURCE_DIR}/vendor/XKCP/lib/common
    )
    target_sources(sha3 PRIVATE
        ${XKCP_TIMES8_DIR}/KeccakP-1600-times8-SIMD512.c
    )
    # Disable -Werror for unused-variable in XKCP code
    set_source_files_properties(
        ${XKCP_TIMES8_DIR}/KeccakP-1600-times8-SIMD512.c
        PROPERTIES COMPILE_FLAGS "-Wno-error=unused-variable"
    )
  else()
    message(STATUS "Optional XKCP AVX512 kernel not found at ${XKCP_TIMES8_DIR}, skipping integration")
  endif()
  # Always add stub include path for common XKCP headers (e.g., KeccakP-1600-times8-SnP.h)
  target_include_directories(sha3 PRIVATE
      ${CMAKE_CURRENT_SOURCE_DIR}/vendor/XKCP/lib/common
  )
  # Note: AVX-512 KeccakP third-party sources have been removed

# Set warning levels
# Set warning levels
target_compile_options(sha3 PRIVATE
    -Wall -Wextra -Wpedantic -Werror
)
## Performance optimizations: enable aggressive compile flags for SHA-3
target_compile_options(sha3 PRIVATE
    -Ofast
    -march=native
    -funroll-loops
    -fomit-frame-pointer
)

# Install headers
install(FILES include/sha3.h DESTINATION include)

## Install library
## Disable link-time optimization (LTO) to avoid creating temp files in /tmp
set_target_properties(sha3 PROPERTIES INTERPROCEDURAL_OPTIMIZATION OFF)

install(TARGETS sha3
        EXPORT sha3Targets
        ARCHIVE DESTINATION lib
        LIBRARY DESTINATION lib
        RUNTIME DESTINATION bin)

# Generate and install package files
include(CMakePackageConfigHelpers)
write_basic_package_version_file(
    "${CMAKE_CURRENT_BINARY_DIR}/sha3ConfigVersion.cmake"
    VERSION ${PROJECT_VERSION}
    COMPATIBILITY SameMajorVersion
)

configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/sha3Config.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/sha3Config.cmake"
    @ONLY
)

install(
    FILES
        "${CMAKE_CURRENT_BINARY_DIR}/sha3Config.cmake"
        "${CMAKE_CURRENT_BINARY_DIR}/sha3ConfigVersion.cmake"
    DESTINATION lib/cmake/sha3
)

# Install exported targets for CMake
install(
    EXPORT sha3Targets
    FILE sha3Targets.cmake
    DESTINATION lib/cmake/sha3
)

# Install license file
install(FILES ${CMAKE_CURRENT_SOURCE_DIR}/LICENSE DESTINATION .)

# Enable testing and examples
option(SHA3_BUILD_TESTS "Build tests for SHA3 library" ON)
option(SHA3_BUILD_EXAMPLES "Build examples for SHA3 library" ON)

# Optional: tests
if(SHA3_BUILD_TESTS)
    # Enable testing
    enable_testing()
    
    # Add test executable
    add_executable(test_sha3 tests/test_sha3.c)
    target_link_libraries(test_sha3 PRIVATE sha3)
    set_target_properties(test_sha3 PROPERTIES INTERPROCEDURAL_OPTIMIZATION ON)
    # Merkle tree tests
    add_executable(test_merkle tests/test_merkle.c)
    target_link_libraries(test_merkle PRIVATE sha3 Threads::Threads)
    set_target_properties(test_merkle PROPERTIES INTERPROCEDURAL_OPTIMIZATION ON)
    
    # Add test
    add_test(NAME test_sha3 COMMAND test_sha3)
    add_test(NAME test_merkle COMMAND test_merkle)
endif()

# Optional: examples
# Optional: examples
if(SHA3_BUILD_EXAMPLES)
    # Parallel benchmark: measure throughput of sha3_hash_parallel across threads
    add_executable(sha3_parallel_benchmark examples/sha3_parallel_benchmark.c)
    target_link_libraries(sha3_parallel_benchmark PRIVATE sha3 Threads::Threads)
    target_compile_options(sha3_parallel_benchmark PRIVATE -Ofast -march=native -funroll-loops -fomit-frame-pointer)

    set_target_properties(
        sha3_parallel_benchmark
        PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin"
    )
    # Enable link-time optimization for example
    set_target_properties(
        sha3_parallel_benchmark
        PROPERTIES INTERPROCEDURAL_OPTIMIZATION ON
    )
    # Merkle tree build benchmark example
    add_executable(sha3_merkle_benchmark examples/sha3_merkle_benchmark.c)
    target_link_libraries(sha3_merkle_benchmark PRIVATE sha3 Threads::Threads)
    target_compile_options(sha3_merkle_benchmark PRIVATE -Ofast -march=native -funroll-loops -fomit-frame-pointer)
    set_target_properties(
        sha3_merkle_benchmark
        PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin"
    )
    set_target_properties(
        sha3_merkle_benchmark
        PROPERTIES INTERPROCEDURAL_OPTIMIZATION ON
    )
endif()