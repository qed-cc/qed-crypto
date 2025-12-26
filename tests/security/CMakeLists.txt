cmake_minimum_required(VERSION 3.16)

# Security Test Suite
project(security_tests)

# Test for zero-knowledge property
add_executable(test_zk_property test_zk_property.c)
target_compile_options(test_zk_property PRIVATE -Wall -Wextra)

# Test for PRG security
add_executable(test_prg_security test_prg_security.c)
target_link_libraries(test_prg_security basefold gf128)
target_include_directories(test_prg_security PRIVATE 
    ${CMAKE_SOURCE_DIR}/modules/basefold/include
    ${CMAKE_SOURCE_DIR}/modules/gf128/include
)
target_compile_options(test_prg_security PRIVATE -Wall -Wextra)

# Test for memory safety
add_executable(test_memory_safety test_memory_safety.c)
target_link_libraries(test_memory_safety basefold gf128)
target_include_directories(test_memory_safety PRIVATE 
    ${CMAKE_SOURCE_DIR}/modules/basefold/include
    ${CMAKE_SOURCE_DIR}/modules/gf128/include
)
target_compile_options(test_memory_safety PRIVATE -Wall -Wextra)

# Phase 6 Tests - Zero-Knowledge Trace Hiding
add_executable(test_zk_trace_hiding test_zk_trace_hiding.c)
target_link_libraries(test_zk_trace_hiding basefold gf128 sha3 common)
target_include_directories(test_zk_trace_hiding PRIVATE 
    ${CMAKE_SOURCE_DIR}/modules/basefold/include
    ${CMAKE_SOURCE_DIR}/modules/gf128/include
    ${CMAKE_SOURCE_DIR}/modules/sha3/include
    ${CMAKE_SOURCE_DIR}/modules/common/include
)
target_compile_options(test_zk_trace_hiding PRIVATE -Wall -Wextra)

add_executable(test_original_quadrant test_original_quadrant.c)
target_link_libraries(test_original_quadrant basefold gf128 common)
target_include_directories(test_original_quadrant PRIVATE 
    ${CMAKE_SOURCE_DIR}/modules/basefold/include
    ${CMAKE_SOURCE_DIR}/modules/gf128/include
    ${CMAKE_SOURCE_DIR}/modules/common/include
)
target_compile_options(test_original_quadrant PRIVATE -Wall -Wextra)

add_executable(test_randomness_quality test_randomness_quality.c)
target_link_libraries(test_randomness_quality basefold gf128 common m)
target_include_directories(test_randomness_quality PRIVATE 
    ${CMAKE_SOURCE_DIR}/modules/basefold/include
    ${CMAKE_SOURCE_DIR}/modules/gf128/include
    ${CMAKE_SOURCE_DIR}/modules/common/include
)
target_compile_options(test_randomness_quality PRIVATE -Wall -Wextra)

add_executable(test_soundness test_soundness.c)
target_link_libraries(test_soundness basefold gf128 common)
target_include_directories(test_soundness PRIVATE 
    ${CMAKE_SOURCE_DIR}/modules/basefold/include
    ${CMAKE_SOURCE_DIR}/modules/gf128/include
    ${CMAKE_SOURCE_DIR}/modules/common/include
)
target_compile_options(test_soundness PRIVATE -Wall -Wextra)

add_executable(benchmark_zk benchmark_zk.c)
target_link_libraries(benchmark_zk basefold gf128 common)
target_include_directories(benchmark_zk PRIVATE 
    ${CMAKE_SOURCE_DIR}/modules/basefold/include
    ${CMAKE_SOURCE_DIR}/modules/gf128/include
    ${CMAKE_SOURCE_DIR}/modules/common/include
)
target_compile_options(benchmark_zk PRIVATE -Wall -Wextra)

add_executable(benchmark_multithreaded benchmark_multithreaded.c)
target_link_libraries(benchmark_multithreaded basefold gf128 sha3 common circuit_io evaluator circuit_sha3)
target_include_directories(benchmark_multithreaded PRIVATE 
    ${CMAKE_SOURCE_DIR}/modules/basefold/include
    ${CMAKE_SOURCE_DIR}/modules/gf128/include
    ${CMAKE_SOURCE_DIR}/modules/sha3/include
    ${CMAKE_SOURCE_DIR}/modules/common/include
    ${CMAKE_SOURCE_DIR}/modules/circuit_io/include
    ${CMAKE_SOURCE_DIR}/modules/circuit_evaluator/include
    ${CMAKE_SOURCE_DIR}/modules/circuit_sha3/include
)
target_compile_options(benchmark_multithreaded PRIVATE -Wall -Wextra)
if(OpenMP_C_FOUND)
    target_link_libraries(benchmark_multithreaded OpenMP::OpenMP_C)
endif()

add_executable(benchmark_multithreaded_simple benchmark_multithreaded_simple.c)
target_link_libraries(benchmark_multithreaded_simple basefold gf128 common)
target_include_directories(benchmark_multithreaded_simple PRIVATE 
    ${CMAKE_SOURCE_DIR}/modules/basefold/include
    ${CMAKE_SOURCE_DIR}/modules/gf128/include
    ${CMAKE_SOURCE_DIR}/modules/common/include
)
target_compile_options(benchmark_multithreaded_simple PRIVATE -Wall -Wextra)
if(OpenMP_C_FOUND)
    target_link_libraries(benchmark_multithreaded_simple OpenMP::OpenMP_C)
endif()

# Add tests to CTest
enable_testing()
add_test(NAME ZeroKnowledgeProperty COMMAND test_zk_property WORKING_DIRECTORY ${CMAKE_BINARY_DIR})
add_test(NAME PRGSecurity COMMAND test_prg_security)
add_test(NAME MemorySafety COMMAND test_memory_safety)

# Phase 6 tests
add_test(NAME ZKTraceHiding COMMAND test_zk_trace_hiding)
add_test(NAME OriginalQuadrantPreservation COMMAND test_original_quadrant)
add_test(NAME RandomnessQuality COMMAND test_randomness_quality)
add_test(NAME Soundness COMMAND test_soundness)
add_test(NAME ZKBenchmark COMMAND benchmark_zk)

# Security fixes verification tests
add_executable(test_basefold_security test_basefold_security.c)
target_link_libraries(test_basefold_security
    basefold
    gf128
    circuit_evaluator
    common
)
target_include_directories(test_basefold_security PRIVATE 
    ${CMAKE_SOURCE_DIR}/modules/basefold/include
    ${CMAKE_SOURCE_DIR}/modules/gf128/include
    ${CMAKE_SOURCE_DIR}/modules/circuit_evaluator/include
    ${CMAKE_SOURCE_DIR}/modules/common/include
    ${CMAKE_SOURCE_DIR}/apps/gate_computer/src
)
target_compile_options(test_basefold_security PRIVATE -Wall -Wextra)

# Add security test to CTest
add_test(NAME BaseFoldSecurity COMMAND test_basefold_security)