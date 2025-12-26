# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

cmake_minimum_required(VERSION 3.16)
project(cmptr_stream C)

# Cmptr Stream - Ultra-low latency quantum-secure stream cipher

# Library sources
set(CMPTR_STREAM_SOURCES
    src/cmptr_stream.c
)

# Create library
add_library(cmptr_stream ${CMPTR_STREAM_SOURCES})

# Include directories
target_include_directories(cmptr_stream
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src
)

# Dependencies
target_link_libraries(cmptr_stream
    PUBLIC
        sha3
    PRIVATE
        m  # Math library
)

# Set C standard
set_target_properties(cmptr_stream PROPERTIES
    C_STANDARD 99
    C_STANDARD_REQUIRED ON
    C_EXTENSIONS OFF
)

# Compiler optimizations for low latency
target_compile_options(cmptr_stream PRIVATE
    $<$<C_COMPILER_ID:GNU,Clang>:-Wall -Wextra -Wpedantic>
    $<$<CONFIG:Release>:-O3 -march=native>
)

# Check for AVX-512 support
include(CheckCCompilerFlag)
check_c_compiler_flag("-mavx512f" COMPILER_SUPPORTS_AVX512)
if(COMPILER_SUPPORTS_AVX512)
    target_compile_options(cmptr_stream PRIVATE -mavx512f)
    target_compile_definitions(cmptr_stream PRIVATE HAVE_AVX512)
endif()

# Build examples if requested
option(BUILD_CMPTR_STREAM_EXAMPLES "Build Cmptr Stream examples" ON)
if(BUILD_CMPTR_STREAM_EXAMPLES)
    add_subdirectory(examples)
endif()

# Build tests if requested
option(BUILD_CMPTR_STREAM_TESTS "Build Cmptr Stream tests" ON)
if(BUILD_CMPTR_STREAM_TESTS)
    add_subdirectory(tests)
endif()