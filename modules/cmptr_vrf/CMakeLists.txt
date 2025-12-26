# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

cmake_minimum_required(VERSION 3.12)

# Create the cmptr_vrf library
add_library(cmptr_vrf STATIC
    src/cmptr_vrf.c
)

# Set include directories
target_include_directories(cmptr_vrf
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src
)

# Link dependencies
target_link_libraries(cmptr_vrf
    PUBLIC
        sha3
        common
)

# Set C standard
set_target_properties(cmptr_vrf PROPERTIES
    C_STANDARD 99
    C_STANDARD_REQUIRED ON
)

# Build examples if requested
option(BUILD_CMPTR_VRF_EXAMPLES "Build Cmptr VRF examples" ON)
if(BUILD_CMPTR_VRF_EXAMPLES)
    add_subdirectory(examples)
endif()

# Build tests if testing is enabled
if(BUILD_TESTING)
    add_subdirectory(tests)
endif()

# Installation
install(TARGETS cmptr_vrf
    EXPORT cmptr_vrfTargets
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
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/cmptr_vrfConfig.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/cmptr_vrfConfig.cmake"
    INSTALL_DESTINATION lib/cmake/cmptr_vrf
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/cmptr_vrfConfig.cmake"
    DESTINATION lib/cmake/cmptr_vrf
)