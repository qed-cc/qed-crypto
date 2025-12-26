# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

cmake_minimum_required(VERSION 3.12)

# Create the cmptr_channel library
add_library(cmptr_channel STATIC
    src/cmptr_channel.c
)

# Set include directories
target_include_directories(cmptr_channel
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src
)

# Link dependencies
target_link_libraries(cmptr_channel
    PUBLIC
        cmptr_stream
        sha3
        common
)

# Set C standard
set_target_properties(cmptr_channel PROPERTIES
    C_STANDARD 99
    C_STANDARD_REQUIRED ON
)

# Build examples if requested
option(BUILD_CMPTR_CHANNEL_EXAMPLES "Build Cmptr Channel examples" ON)
if(BUILD_CMPTR_CHANNEL_EXAMPLES)
    add_subdirectory(examples)
endif()

# Build tests if testing is enabled
if(BUILD_TESTING)
    add_subdirectory(tests)
endif()

# Installation
install(TARGETS cmptr_channel
    EXPORT cmptr_channelTargets
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
    RUNTIME DESTINATION bin
    INCLUDES DESTINATION include
)

install(DIRECTORY include/
    DESTINATION include
    FILES_MATCHING PATTERN "*.h"
)

# Export targets - commented out for now due to dependency issues
# install(EXPORT cmptr_channelTargets
#     FILE cmptr_channelTargets.cmake
#     NAMESPACE cmptr::
#     DESTINATION lib/cmake/cmptr_channel
# )

# Create config file
include(CMakePackageConfigHelpers)
configure_package_config_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/cmptr_channelConfig.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/cmptr_channelConfig.cmake"
    INSTALL_DESTINATION lib/cmake/cmptr_channel
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/cmptr_channelConfig.cmake"
    DESTINATION lib/cmake/cmptr_channel
)