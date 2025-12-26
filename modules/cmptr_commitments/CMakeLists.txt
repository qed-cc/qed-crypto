# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

cmake_minimum_required(VERSION 3.16)
project(cmptr_commitments C)

# Cmptr Commitments - Vector commitments with constant-size proofs

# Library sources
set(CMPTR_COMMITMENTS_SOURCES
    src/cmptr_commitments.c
)

# Create library
add_library(cmptr_commitments ${CMPTR_COMMITMENTS_SOURCES})

# Include directories
target_include_directories(cmptr_commitments
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src
)

# Dependencies
target_link_libraries(cmptr_commitments
    PUBLIC
        basefold_raa  # For recursive STARKs
        cmptr_trees   # For Merkle tree base
        sha3
    PRIVATE
        m  # Math library
)

# Set C standard
set_target_properties(cmptr_commitments PROPERTIES
    C_STANDARD 99
    C_STANDARD_REQUIRED ON
    C_EXTENSIONS OFF
)

# Compiler optimizations
target_compile_options(cmptr_commitments PRIVATE
    $<$<C_COMPILER_ID:GNU,Clang>:-Wall -Wextra -Wpedantic>
    $<$<CONFIG:Release>:-O3 -march=native>
)

# Build examples if requested
option(BUILD_CMPTR_COMMITMENTS_EXAMPLES "Build Cmptr Commitments examples" ON)
if(BUILD_CMPTR_COMMITMENTS_EXAMPLES)
    add_subdirectory(examples)
endif()

# Build tests if requested
option(BUILD_CMPTR_COMMITMENTS_TESTS "Build Cmptr Commitments tests" ON)
if(BUILD_CMPTR_COMMITMENTS_TESTS)
    add_subdirectory(tests)
endif()