# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

cmake_minimum_required(VERSION 3.12)

# Create the cmptr_trees library
add_library(cmptr_trees STATIC
    src/cmptr_trees.c
)

# Set include directories
target_include_directories(cmptr_trees
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src
)

# Link dependencies
target_link_libraries(cmptr_trees
    PUBLIC
        sha3
)

# Set C standard
set_target_properties(cmptr_trees PROPERTIES
    C_STANDARD 99
    C_STANDARD_REQUIRED ON
)

# Check for AVX-512 support
include(CheckCCompilerFlag)
check_c_compiler_flag("-mavx512f" COMPILER_SUPPORTS_AVX512)
if(COMPILER_SUPPORTS_AVX512)
    target_compile_options(cmptr_trees PRIVATE -mavx512f)
    target_compile_definitions(cmptr_trees PRIVATE HAVE_AVX512)
endif()

# Build examples if requested
option(BUILD_CMPTR_TREES_EXAMPLES "Build Cmptr Trees examples" ON)
if(BUILD_CMPTR_TREES_EXAMPLES)
    add_subdirectory(examples)
endif()

# Build tests if testing is enabled
if(BUILD_TESTING)
    add_subdirectory(tests)
endif()

# Installation
install(TARGETS cmptr_trees
    EXPORT cmptr_treesTargets
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
    RUNTIME DESTINATION bin
    INCLUDES DESTINATION include
)

install(DIRECTORY include/
    DESTINATION include
    FILES_MATCHING PATTERN "*.h"
)

# Create config file
include(CMakePackageConfigHelpers)
configure_package_config_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/cmptr_treesConfig.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/cmptr_treesConfig.cmake"
    INSTALL_DESTINATION lib/cmake/cmptr_trees
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/cmptr_treesConfig.cmake"
    DESTINATION lib/cmake/cmptr_trees
)