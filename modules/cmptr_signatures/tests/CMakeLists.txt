# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# RAS Tests

# Basic functionality test
add_executable(test_ras_basic test_basic.c)
target_link_libraries(test_ras_basic PRIVATE ras)
add_test(NAME ras_basic COMMAND test_ras_basic)

# Aggregation test
add_executable(test_ras_aggregation test_aggregation.c)
target_link_libraries(test_ras_aggregation PRIVATE ras)
add_test(NAME ras_aggregation COMMAND test_ras_aggregation)

# Serialization test
add_executable(test_ras_serialization test_serialization.c)
target_link_libraries(test_ras_serialization PRIVATE ras)
add_test(NAME ras_serialization COMMAND test_ras_serialization)