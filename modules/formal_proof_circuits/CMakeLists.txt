# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

project(formal_proof_circuits C)

# Find required dependencies
find_package(basefold_raa REQUIRED)
find_package(gf128 REQUIRED)
find_package(sha3 REQUIRED)
find_package(circuit_evaluator REQUIRED)

# Source files
set(SOURCES
    src/fopl_parser.c
    src/circuit_compiler.c
    src/proof_theories.c
    src/basefold_integration.c
    src/witness_generator.c
)

# Create library
add_library(formal_proof_circuits ${SOURCES})

# Include directories
target_include_directories(formal_proof_circuits PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)

# Link dependencies
target_link_libraries(formal_proof_circuits
    PUBLIC
        basefold_raa::basefold_raa
        gf128::gf128
        sha3::sha3
        circuit_evaluator::circuit_evaluator
    PRIVATE
        m  # Math library for SAT solver
)

# Set properties
set_target_properties(formal_proof_circuits PROPERTIES
    C_STANDARD 99
    C_STANDARD_REQUIRED ON
    C_EXTENSIONS OFF
)

# Apply compiler warnings
include(${CMAKE_SOURCE_DIR}/cmake/CompilerWarnings.cmake)
set_project_warnings(formal_proof_circuits)

# Installation
install(TARGETS formal_proof_circuits
    EXPORT formal_proof_circuitsTargets
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
    RUNTIME DESTINATION bin
    INCLUDES DESTINATION include
)

install(DIRECTORY include/ DESTINATION include)

# Export targets
install(EXPORT formal_proof_circuitsTargets
    FILE formal_proof_circuitsTargets.cmake
    NAMESPACE formal_proof_circuits::
    DESTINATION lib/cmake/formal_proof_circuits
)

# Create config file
include(CMakePackageConfigHelpers)
configure_package_config_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/formal_proof_circuitsConfig.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/formal_proof_circuitsConfig.cmake"
    INSTALL_DESTINATION lib/cmake/formal_proof_circuits
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/formal_proof_circuitsConfig.cmake"
    DESTINATION lib/cmake/formal_proof_circuits
)

# Tests
option(BUILD_TESTING "Build tests" ON)
if(BUILD_TESTING)
    add_subdirectory(tests)
endif()