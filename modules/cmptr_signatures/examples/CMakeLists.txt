# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# RAS Examples

# Include directories for all examples
include_directories(${CMAKE_SOURCE_DIR}/modules/sha3/include)

# Basic signature demo
add_executable(ras_basic_demo basic_demo.c)
target_link_libraries(ras_basic_demo PRIVATE ras)

# Aggregation demo - shows the power of RAS
add_executable(ras_aggregation_demo aggregation_demo.c)
target_link_libraries(ras_aggregation_demo PRIVATE ras)

# Blockchain consensus demo - 100 validators signing blocks
add_executable(ras_consensus_demo consensus_demo.c)
target_link_libraries(ras_consensus_demo PRIVATE ras sha3)

# Performance benchmark
add_executable(ras_benchmark benchmark.c)
target_link_libraries(ras_benchmark PRIVATE ras m pthread)