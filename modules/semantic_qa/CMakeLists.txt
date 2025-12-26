# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

cmake_minimum_required(VERSION 3.10)
project(semantic_qa C)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)

# Define semantic_qa library sources
set(SEMANTIC_QA_SOURCES
    src/semantic_qa.c
    # src/benchmark_tests.c  # File doesn't exist
)

# Create static library
add_library(semantic_qa STATIC ${SEMANTIC_QA_SOURCES})

# Include directories
target_include_directories(semantic_qa PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)

# Link with required libraries
target_link_libraries(semantic_qa
    PUBLIC
        m  # Math library
)

# Installation rules
install(TARGETS semantic_qa
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
)

install(DIRECTORY include/
    DESTINATION include
)

# Export for use in parent project
set(SEMANTIC_QA_INCLUDE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/include PARENT_SCOPE)
set(SEMANTIC_QA_LIBRARY semantic_qa PARENT_SCOPE)