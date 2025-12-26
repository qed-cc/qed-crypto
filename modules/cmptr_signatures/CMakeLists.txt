# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

cmake_minimum_required(VERSION 3.16)
project(cmptr_signatures C)

# Library sources
set(CMPTR_SIGNATURES_SOURCES
    src/cmptr_core.c
    src/cmptr_keygen.c
    src/cmptr_sign.c
    src/cmptr_verify.c
    src/cmptr_aggregate.c
    src/cmptr_serialize.c
    src/cmptr_circuit.c
)

# Create the library
add_library(cmptr_signatures ${CMPTR_SIGNATURES_SOURCES})

# Include directories
target_include_directories(cmptr_signatures
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src
)

# Dependencies
target_link_libraries(cmptr_signatures
    PUBLIC
        basefold_raa
        sha3
        gf128
    PRIVATE
        m  # Math library
        pthread
)

# Set C standard
set_target_properties(cmptr_signatures PROPERTIES
    C_STANDARD 99
    C_STANDARD_REQUIRED ON
    C_EXTENSIONS OFF
)

# Compiler warnings
target_compile_options(cmptr_signatures PRIVATE
    $<$<C_COMPILER_ID:GNU,Clang>:-Wall -Wextra -Wpedantic>
)

# Enable OpenMP if available
find_package(OpenMP)
if(OpenMP_C_FOUND)
    target_link_libraries(cmptr_signatures PRIVATE OpenMP::OpenMP_C)
endif()

# Build examples if requested
option(BUILD_CMPTR_SIGNATURES_EXAMPLES "Build Cmptr Signatures examples" ON)
if(BUILD_CMPTR_SIGNATURES_EXAMPLES)
    add_subdirectory(examples)
endif()

# Build tests if requested
option(BUILD_CMPTR_SIGNATURES_TESTS "Build Cmptr Signatures tests" ON)
if(BUILD_CMPTR_SIGNATURES_TESTS)
    add_subdirectory(tests)
endif()

# Installation - disabled for now due to export dependencies
# include(GNUInstallDirs)
# 
# install(TARGETS ras
#     EXPORT rasTargets
#     LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
#     ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
#     RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
# )
# 
# install(DIRECTORY include/
#     DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
#     FILES_MATCHING PATTERN "*.h"
# )
# 
# # Export targets
# install(EXPORT rasTargets
#     FILE rasConfig.cmake
#     NAMESPACE ras::
#     DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/ras
# )
# 
# # Configure and install package config
# include(CMakePackageConfigHelpers)
# write_basic_package_version_file(
#     "${CMAKE_CURRENT_BINARY_DIR}/rasConfigVersion.cmake"
#     VERSION 1.0.0
#     COMPATIBILITY AnyNewerVersion
# )