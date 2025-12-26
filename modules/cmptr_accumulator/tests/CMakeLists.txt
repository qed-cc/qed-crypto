# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# CMPTR Accumulator Tests

# Basic functionality test
add_executable(test_accumulator_basic test_basic.c)
target_link_libraries(test_accumulator_basic cmptr_accumulator)
add_test(NAME accumulator_basic COMMAND test_accumulator_basic)

# PoW test
add_executable(test_accumulator_pow test_pow.c)
target_link_libraries(test_accumulator_pow cmptr_accumulator pthread)
add_test(NAME accumulator_pow COMMAND test_accumulator_pow)

# Pruning test
add_executable(test_accumulator_pruning test_pruning.c)
target_link_libraries(test_accumulator_pruning cmptr_accumulator)
add_test(NAME accumulator_pruning COMMAND test_accumulator_pruning)