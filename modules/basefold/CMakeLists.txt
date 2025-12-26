cmake_minimum_required(VERSION 3.10)
project(basefold C)

# Set C standard
set(CMAKE_C_STANDARD 11)

# Include directories (legacy style for now)
include_directories(include)
include_directories(${CMAKE_SOURCE_DIR}/modules/common/include)
include_directories(${CMAKE_SOURCE_DIR}/modules/sha3/include)
include_directories(${CMAKE_SOURCE_DIR}/modules/gf128/include)

# Source files
set(BASEFOLD_SOURCES
    src/basefold_trace.c
    src/prg.c
    src/transcript.c
    src/enc.c
    src/enc_init.c
    src/enc_stream.c
    src/merkle/build.c
    src/merkle/verify.c
    src/gate_sumcheck.c
    src/wiring.c
    src/wiring_sumcheck.c
    src/fold_reduce.c
    src/polynomial_gf128.c
    src/polynomial_domain.c
    src/polynomial_zk.c
    src/polynomial_zk_simple.c
    src/polynomial_zk_multilinear.c
    src/polynomial_zk_proper.c
    src/multilinear.c
    src/vanishing_poly.c
    src/gate_sumcheck_multilinear.c
    src/gate_sumcheck_multilinear_fast.c
    src/multilinear_merkle_proof.c
    src/merkle_commitment.c
    src/sumcheck_merkle_proof.c
    src/field_xor_masking.c
    src/compute_masked_evaluations.c
    src/evaluation_domain.c
    src/extended_domain_utils.c
    src/sumcheck_worker_pool.c
    src/gate_sumcheck_row_major.c
    src/evaluation_path.c
    src/merkle_sumcheck_binding.c
    src/sumcheck_fast_simple.c
    src/binary_ntt_stub.c
)

# Headers
set(BASEFOLD_HEADERS
    include/basefold_trace.h
    include/prg.h
    include/transcript.h
    include/enc.h
    include/merkle/build.h
    include/merkle/verify.h
    include/gate_sumcheck.h
    include/wiring.h
    include/wiring_sumcheck.h
    include/fold_reduce.h
    include/polynomial_gf128.h
    include/multilinear.h
    include/vanishing_poly.h
    include/gate_sumcheck_multilinear.h
    include/gate_sumcheck_zk.h
    include/merkle_commitment.h
    include/evaluation_domain.h
    include/extended_domain_utils.h
    include/evaluation_path.h
    include/merkle_sumcheck_binding.h
    include/binary_ntt.h
)

# Create library
add_library(basefold STATIC ${BASEFOLD_SOURCES} ${BASEFOLD_HEADERS})

# Add AES-NI support for x86_64
if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64")
    target_compile_options(basefold PRIVATE -maes -msse4.1)
    # Add AVX2 and AVX-512 for sumcheck optimization
    # Check if the file uses AVX instructions
    set_source_files_properties(src/gate_sumcheck_multilinear_fast.c 
        PROPERTIES COMPILE_FLAGS "-mavx2 -mavx512f")
    set_source_files_properties(src/sumcheck_worker_pool.c 
        PROPERTIES COMPILE_FLAGS "-mavx2 -mavx512f")
    set_source_files_properties(src/gate_sumcheck_row_major.c 
        PROPERTIES COMPILE_FLAGS "-mavx2 -mavx512f -mavx512vl -mvpclmulqdq")
endif()

# Link pthread for worker threads
find_package(Threads REQUIRED)
target_link_libraries(basefold PRIVATE ${CMAKE_THREAD_LIBS_INIT})

# Link required libraries
target_link_libraries(basefold PRIVATE m)
# Link common module for secure random functionality
target_link_libraries(basefold PRIVATE common)
# Link sha3 module for transcript functionality
target_link_libraries(basefold PRIVATE sha3)
# Link gf128 module for encoding functionality
target_link_libraries(basefold PRIVATE gf128)

# Install rules
install(TARGETS basefold
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
)

install(FILES ${BASEFOLD_HEADERS}
    DESTINATION include
)

# Export for use by other projects (disabled for superbuild to avoid export errors)
# export(TARGETS basefold FILE basefoldTargets.cmake)

# Configuration for find_package
include(CMakePackageConfigHelpers)
configure_package_config_file(
    cmake/basefoldConfig.cmake.in
    ${CMAKE_CURRENT_BINARY_DIR}/basefoldConfig.cmake
    INSTALL_DESTINATION lib/cmake/basefold
)

install(FILES ${CMAKE_CURRENT_BINARY_DIR}/basefoldConfig.cmake
    DESTINATION lib/cmake/basefold
)

# Test targets
if(BUILD_TESTING)
    enable_testing()
    
    # Round-trip test
    add_executable(enc_roundtrip tests/enc_roundtrip.c)
    target_link_libraries(enc_roundtrip basefold)
    add_test(NAME enc_roundtrip COMMAND enc_roundtrip)
    
    # Full-size test
    add_executable(enc_size tests/enc_size.c)
    target_link_libraries(enc_size basefold)
    add_test(NAME enc_size COMMAND enc_size)
    
    # Merkle unit tests
    add_executable(merkle_unit tests/merkle/test_merkle_unit.c)
    target_link_libraries(merkle_unit basefold)
    add_test(NAME merkle_unit COMMAND merkle_unit)
    
    # Merkle smoke test
    add_executable(merkle_smoke tests/merkle/test_merkle_smoke.c)
    target_link_libraries(merkle_smoke basefold)
    add_test(NAME merkle_smoke COMMAND merkle_smoke)
    
    # SumCheck basic tests
    add_executable(sumcheck_basic tests/test_sumcheck_basic.c)
    target_link_libraries(sumcheck_basic basefold)
    add_test(NAME sumcheck_basic COMMAND sumcheck_basic)
    
    # Polynomial tests
    add_executable(test_polynomial tests/test_polynomial.c)
    target_link_libraries(test_polynomial basefold)
    add_test(NAME test_polynomial COMMAND test_polynomial)
    
    # Multilinear polynomial tests
    add_executable(test_multilinear tests/test_multilinear.c)
    target_link_libraries(test_multilinear basefold)
    add_test(NAME test_multilinear COMMAND test_multilinear)
    
    # Vanishing polynomial tests
    add_executable(test_vanishing_poly tests/test_vanishing_poly.c)
    target_link_libraries(test_vanishing_poly basefold)
    add_test(NAME test_vanishing_poly COMMAND test_vanishing_poly)
    
    # Multilinear gate sumcheck tests
    add_executable(test_gate_sumcheck_ml tests/test_gate_sumcheck_ml.c)
    target_link_libraries(test_gate_sumcheck_ml basefold)
    add_test(NAME test_gate_sumcheck_ml COMMAND test_gate_sumcheck_ml)
    
    # Merkle-SumCheck binding verification tests
    add_executable(test_merkle_sumcheck_binding tests/test_merkle_sumcheck_binding.c)
    target_link_libraries(test_merkle_sumcheck_binding basefold)
    add_test(NAME test_merkle_sumcheck_binding COMMAND test_merkle_sumcheck_binding)
    
    # Set test properties
    set_tests_properties(enc_roundtrip PROPERTIES TIMEOUT 30)
    set_tests_properties(enc_size PROPERTIES TIMEOUT 120)
    set_tests_properties(merkle_unit PROPERTIES TIMEOUT 60)
    set_tests_properties(merkle_smoke PROPERTIES TIMEOUT 300)
    set_tests_properties(sumcheck_basic PROPERTIES TIMEOUT 60)
    set_tests_properties(test_polynomial PROPERTIES TIMEOUT 30)
    set_tests_properties(test_multilinear PROPERTIES TIMEOUT 30)
    set_tests_properties(test_vanishing_poly PROPERTIES TIMEOUT 30)
    set_tests_properties(test_gate_sumcheck_ml PROPERTIES TIMEOUT 30)
    set_tests_properties(test_merkle_sumcheck_binding PROPERTIES TIMEOUT 30)
endif()