# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# CMPTR Accumulator Module
# Implements recursive proof accumulators with PARKED/ACTIVE token states
# for scalable zero-knowledge blockchain systems

cmake_minimum_required(VERSION 3.16)
project(cmptr_accumulator VERSION 1.0.0 LANGUAGES C)

# Export compile commands for tools
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# Create library
add_library(cmptr_accumulator
    src/accumulator.c
    src/nullifier_set.c
    src/kernel_set.c
    src/token_state.c
    src/pruning.c
    src/hierarchical_tps.c
    src/aggregator.c
    src/proof_generator.c
    src/block_producer.c
)

# Set include directories
target_include_directories(cmptr_accumulator
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src
)

# Add include directories from dependencies
if(TARGET sha3)
    # Manually add sha3 include directory
    target_include_directories(cmptr_accumulator PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/../sha3/include)
    target_compile_definitions(cmptr_accumulator PRIVATE HAS_SHA3)
endif()
if(TARGET basefold_raa)
    target_include_directories(cmptr_accumulator PRIVATE $<TARGET_PROPERTY:basefold_raa,INTERFACE_INCLUDE_DIRECTORIES>)
    target_compile_definitions(cmptr_accumulator PRIVATE HAS_BASEFOLD_RAA)
endif()

# Link dependencies - Check which are available
set(CMPTR_ACC_PUBLIC_LIBS "")
set(CMPTR_ACC_PRIVATE_LIBS "")

if(TARGET basefold_raa)
    list(APPEND CMPTR_ACC_PUBLIC_LIBS basefold_raa)
endif()

if(TARGET sha3)
    list(APPEND CMPTR_ACC_PUBLIC_LIBS sha3)
endif()

if(TARGET gf128)
    list(APPEND CMPTR_ACC_PUBLIC_LIBS gf128)
endif()

if(TARGET circuit_generator)
    list(APPEND CMPTR_ACC_PUBLIC_LIBS circuit_generator)
endif()

if(TARGET common)
    list(APPEND CMPTR_ACC_PRIVATE_LIBS common)
endif()

# Always need these
list(APPEND CMPTR_ACC_PRIVATE_LIBS pthread m)

target_link_libraries(cmptr_accumulator
    PUBLIC ${CMPTR_ACC_PUBLIC_LIBS}
    PRIVATE ${CMPTR_ACC_PRIVATE_LIBS}
)

# Set C standard
set_target_properties(cmptr_accumulator PROPERTIES
    C_STANDARD 99
    C_STANDARD_REQUIRED ON
    C_EXTENSIONS OFF
)

# Apply project compiler warnings if available
if(COMMAND apply_project_warnings)
    apply_project_warnings(cmptr_accumulator)
endif()

# Installation rules
install(TARGETS cmptr_accumulator
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
    RUNTIME DESTINATION bin
    INCLUDES DESTINATION include
)

install(DIRECTORY include/
    DESTINATION include
    FILES_MATCHING PATTERN "*.h"
)

# Skip complex install configuration for now

# Build tests
if(BUILD_TESTING)
    add_subdirectory(tests)
endif()

# Build examples
option(BUILD_ACCUMULATOR_EXAMPLES "Build cmptr_accumulator examples" ON)
if(BUILD_ACCUMULATOR_EXAMPLES)
    add_subdirectory(examples)
endif()