# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

cmake_minimum_required(VERSION 3.10)
project(basefold_raa)

# BaseFold RAA hybrid proof system
# Combines BaseFold's sumcheck with RAA encoding for optimal performance

# Source files
set(BASEFOLD_RAA_SOURCES
    src/raa_encode.c
    src/raa_commit.c
    src/basefold_raa_prove.c
    src/basefold_raa_verify.c
    src/raa_utils.c
    src/state_transition_circuit.c
    src/circuit_witness_generator.c
    src/gate_witness_generator.c
    src/constraint_polynomial.c
    src/raa_ras_integration.c  # RAS integration functions
    # src/circular_recursion.c  # Disabled - needs proper circuit types
)

# Create library
add_library(basefold_raa STATIC ${BASEFOLD_RAA_SOURCES})

# Include directories
target_include_directories(basefold_raa 
    PUBLIC 
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src
        ${CMAKE_SOURCE_DIR}/modules/basefold/include  # Add basefold includes explicitly
        ${CMAKE_SOURCE_DIR}/modules/sha3/include     # Add sha3 includes
        ${CMAKE_SOURCE_DIR}/modules/common/include   # Add common includes
        ${CMAKE_SOURCE_DIR}/modules/gf128/include    # Add gf128 includes
        ${CMAKE_SOURCE_DIR}/modules/circuit_generator/include  # For recursive circuits
)

# Link dependencies
target_link_libraries(basefold_raa
    PUBLIC
        gf128
        sha3
        basefold  # For sumcheck and binary NTT
        common    # For secure random
        circuit_generator  # For recursive circuits
)

# Set properties
set_target_properties(basefold_raa PROPERTIES
    C_STANDARD 99
    C_STANDARD_REQUIRED YES
    C_EXTENSIONS NO
)

# Enable optimizations
if(CMAKE_BUILD_TYPE STREQUAL "Release")
    target_compile_options(basefold_raa PRIVATE -O3 -march=native)
endif()

# Enable comprehensive compiler warnings
include(${CMAKE_SOURCE_DIR}/cmake/CompilerWarnings.cmake)
enable_cmptr_warnings(basefold_raa)

# OpenMP support for parallel encoding
find_package(OpenMP)
if(OpenMP_C_FOUND)
    target_link_libraries(basefold_raa PUBLIC OpenMP::OpenMP_C)
endif()

# Build tests
if(BUILD_TESTING)
    add_subdirectory(tests)
endif()

# Export configuration
include(CMakePackageConfigHelpers)
configure_package_config_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/basefold_raaConfig.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/basefold_raaConfig.cmake"
    INSTALL_DESTINATION lib/cmake/basefold_raa
)