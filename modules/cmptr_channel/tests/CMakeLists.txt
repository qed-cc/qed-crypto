# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Basic test
add_executable(test_cmptr_channel test_basic.c)
target_link_libraries(test_cmptr_channel PRIVATE cmptr_channel)
add_test(NAME cmptr_channel_basic COMMAND test_cmptr_channel)