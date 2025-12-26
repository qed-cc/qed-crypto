# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Basic test
add_executable(test_cmptr_exchange test_basic.c)
target_link_libraries(test_cmptr_exchange PRIVATE cmptr_exchange)
add_test(NAME cmptr_exchange_basic COMMAND test_cmptr_exchange)