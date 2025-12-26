# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Basic test
add_executable(test_cmptr_trees test_basic.c)
target_link_libraries(test_cmptr_trees PRIVATE cmptr_trees)
add_test(NAME cmptr_trees_basic COMMAND test_cmptr_trees)