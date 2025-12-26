# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

set(MODULE_NAME cmptr_blockchain)

# Sources
set(SOURCES
    src/blockchain.c
    src/aggregator.c
    src/generator.c
    src/producer.c
    src/validator.c
    src/consensus.c
    src/networking.c
    src/storage_tiers.c
    src/sync_protocol.c
    src/node_lifecycle.c
)

# Create library
add_library(${MODULE_NAME} STATIC ${SOURCES})

# Add compile definitions for pthread features
target_compile_definitions(${MODULE_NAME} PRIVATE _GNU_SOURCE)

# Include directories
target_include_directories(${MODULE_NAME}
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
)

# Link dependencies
target_link_libraries(${MODULE_NAME}
    PUBLIC
        cmptr_accumulator
        common
        pthread
    PRIVATE
        $<$<BOOL:${SHA3_FOUND}>:sha3>
)

# Apply warnings
if(COMMAND apply_project_warnings)
    apply_project_warnings(${MODULE_NAME})
endif()

# Examples
option(BUILD_EXAMPLES "Build example programs" ON)
if(BUILD_EXAMPLES)
    add_subdirectory(examples)
endif()

# Tests
if(BUILD_TESTS)
    add_subdirectory(tests)
endif()

# Install
install(TARGETS ${MODULE_NAME}
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
)

install(DIRECTORY include/
    DESTINATION include
    FILES_MATCHING PATTERN "*.h"
)

# Export
install(FILES cmake/${MODULE_NAME}Config.cmake
    DESTINATION lib/cmake/${MODULE_NAME}
)

message(STATUS "Added module: ${MODULE_NAME}")
message(STATUS "Building Cmptr Blockchain: Hierarchical blockchain with 1M TPS")
message(STATUS "  Node types: Aggregator, Generator, Producer, Validator")
message(STATUS "  Storage tiers: Archive, Full, Light, Ultra-Light")