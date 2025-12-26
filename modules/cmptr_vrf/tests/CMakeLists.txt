# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Basic test
add_executable(test_cmptr_vrf test_basic.c)
target_link_libraries(test_cmptr_vrf PRIVATE cmptr_vrf)
add_test(NAME cmptr_vrf_basic COMMAND test_cmptr_vrf)