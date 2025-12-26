# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

cmake_minimum_required(VERSION 3.12)

# Create the cmptr_exchange library
add_library(cmptr_exchange STATIC
    src/cmptr_exchange.c
)

# Set include directories
target_include_directories(cmptr_exchange
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src
)

# Link dependencies
target_link_libraries(cmptr_exchange
    PUBLIC
        sha3
        common
)

# Set C standard
set_target_properties(cmptr_exchange PROPERTIES
    C_STANDARD 99
    C_STANDARD_REQUIRED ON
)

# Build examples if requested
option(BUILD_CMPTR_EXCHANGE_EXAMPLES "Build Cmptr Exchange examples" ON)
if(BUILD_CMPTR_EXCHANGE_EXAMPLES)
    add_subdirectory(examples)
endif()

# Build tests if testing is enabled
if(BUILD_TESTING)
    add_subdirectory(tests)
endif()

# Installation
install(TARGETS cmptr_exchange
    EXPORT cmptr_exchangeTargets
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
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/cmptr_exchangeConfig.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/cmptr_exchangeConfig.cmake"
    INSTALL_DESTINATION lib/cmake/cmptr_exchange
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/cmptr_exchangeConfig.cmake"
    DESTINATION lib/cmake/cmptr_exchange
)