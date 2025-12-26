# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# CMPTR Accumulator Examples

# Simple demo without PoW
add_executable(simple_demo simple_demo.c)
target_link_libraries(simple_demo cmptr_accumulator)

# Basic accumulator demo
add_executable(accumulator_demo accumulator_demo.c)
target_link_libraries(accumulator_demo cmptr_accumulator)

# Mining demo
add_executable(accumulator_mining mining_demo.c)
target_link_libraries(accumulator_mining cmptr_accumulator pthread)

# High TPS demo
add_executable(accumulator_tps tps_demo.c)
target_link_libraries(accumulator_tps cmptr_accumulator pthread)

# Blockchain demo
add_executable(accumulator_blockchain blockchain_demo.c)
target_link_libraries(accumulator_blockchain cmptr_accumulator pthread)