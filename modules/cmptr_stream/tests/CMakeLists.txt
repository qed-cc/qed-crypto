# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Basic test
add_executable(test_cmptr_stream test_basic.c)
target_link_libraries(test_cmptr_stream PRIVATE cmptr_stream)
add_test(NAME cmptr_stream_basic COMMAND test_cmptr_stream)