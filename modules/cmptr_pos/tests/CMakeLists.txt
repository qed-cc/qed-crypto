# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Enable testing
enable_testing()

# PoS Core Tests
add_executable(test_pos_core test_pos_core.c)
target_link_libraries(test_pos_core
    PRIVATE
        cmptr_pos
        cmptr_accumulator
        cmptr_blockchain
        basefold_raa
        common
        pthread
)
add_test(NAME test_pos_core COMMAND test_pos_core)

# Verkle Commitment Tests
add_executable(test_verkle test_verkle.c)
target_link_libraries(test_verkle
    PRIVATE
        cmptr_pos
        cmptr_accumulator
        cmptr_blockchain
        basefold_raa
        common
        pthread
)
add_test(NAME test_verkle COMMAND test_verkle)

# Lattice VRF Tests
add_executable(test_lattice_vrf test_lattice_vrf.c)
target_link_libraries(test_lattice_vrf
    PRIVATE
        cmptr_pos
        cmptr_accumulator
        cmptr_blockchain
        basefold_raa
        common
        pthread
)
add_test(NAME test_lattice_vrf COMMAND test_lattice_vrf)

# Optimization Tests
add_executable(test_optimizations test_optimizations.c)
target_link_libraries(test_optimizations
    PRIVATE
        cmptr_pos
        basefold_raa
        sha3
        common
        pthread
        m
)
add_test(NAME test_optimizations COMMAND test_optimizations)