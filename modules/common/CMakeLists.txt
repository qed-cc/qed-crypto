# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Common utilities module
cmake_minimum_required(VERSION 3.16)

# Create the common library
add_library(common
    src/secure_random.c
    src/input_validation.c
    src/logger.c
    # src/test_random.c  # File doesn't exist
)

# Set up include directories
target_include_directories(common 
    PUBLIC include
)

# Link system libraries needed for secure random generation
if(UNIX AND NOT APPLE)
    # Linux - link pthread for logger
    target_link_libraries(common pthread)
endif()

if(APPLE)
    # macOS - use /dev/urandom
endif()

if(WIN32)
    # Windows - would use CryptGenRandom, but not implemented yet
    target_link_libraries(common advapi32)
endif()

# Set compiler flags for this module
target_compile_options(common PRIVATE
    -Wall
    -Wextra
    -Wformat
    -Wformat-security
    -fstack-protector-strong
)

# Add feature test macros for secure random functions
target_compile_definitions(common PRIVATE
    _DEFAULT_SOURCE
    _GNU_SOURCE
)

# Install headers
install(FILES
    include/secure_random.h
    include/secure_random_compat.h
    include/input_validation.h
    include/logger.h
    # include/test_random.h  # File doesn't exist
    DESTINATION include
)

# Install library
install(TARGETS common
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
)

# Optional: Build tests if testing is enabled
if(BUILD_TESTING AND EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/tests/CMakeLists.txt")
    add_subdirectory(tests)
endif()