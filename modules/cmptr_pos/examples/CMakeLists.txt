# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# PoS Demo
add_executable(pos_demo pos_demo.c)
target_compile_definitions(pos_demo PRIVATE _GNU_SOURCE)
target_link_libraries(pos_demo
    PRIVATE
        cmptr_pos
        cmptr_accumulator
        cmptr_blockchain
        basefold_raa
        common
        pthread
)

# Validator Demo
add_executable(pos_validator_demo pos_validator_demo.c)
target_compile_definitions(pos_validator_demo PRIVATE _GNU_SOURCE)
target_link_libraries(pos_validator_demo
    PRIVATE
        cmptr_pos
        cmptr_accumulator
        cmptr_blockchain
        basefold_raa
        common
        pthread
)

# SHA3-only PoS Demo
add_executable(pos_sha3_only_demo pos_sha3_only_demo.c)
target_compile_definitions(pos_sha3_only_demo PRIVATE _GNU_SOURCE)
target_link_libraries(pos_sha3_only_demo
    PRIVATE
        cmptr_pos
        cmptr_accumulator
        cmptr_blockchain
        basefold_raa
        sha3
        common
        pthread
)

# PoS v2 Complete Demo
add_executable(pos_v2_complete_demo pos_v2_complete_demo.c)
target_compile_definitions(pos_v2_complete_demo PRIVATE _GNU_SOURCE)
target_link_libraries(pos_v2_complete_demo
    PRIVATE
        cmptr_pos
        cmptr_accumulator
        cmptr_blockchain
        basefold_raa
        common
        pthread
)

# Recursive Committee Demo
add_executable(recursive_committee_demo recursive_committee_demo.c)
target_compile_definitions(recursive_committee_demo PRIVATE _GNU_SOURCE)
target_link_libraries(recursive_committee_demo
    PRIVATE
        cmptr_pos
        cmptr_accumulator
        cmptr_blockchain
        basefold_raa
        sha3
        common
        pthread
)

# Instant Sync Demo
add_executable(instant_sync_demo instant_sync_demo.c)
target_compile_definitions(instant_sync_demo PRIVATE _GNU_SOURCE)
target_link_libraries(instant_sync_demo
    PRIVATE
        cmptr_pos
        cmptr_accumulator
        cmptr_blockchain
        basefold_raa
        sha3
        common
        pthread
)

# Proof Trigger Demo
add_executable(proof_trigger_demo proof_trigger_demo.c)
target_compile_definitions(proof_trigger_demo PRIVATE _GNU_SOURCE)
target_link_libraries(proof_trigger_demo
    PRIVATE
        cmptr_pos
        pthread
)

# Streaming VRF Demo
add_executable(streaming_vrf_demo streaming_vrf_demo.c)
target_compile_definitions(streaming_vrf_demo PRIVATE _GNU_SOURCE)
target_link_libraries(streaming_vrf_demo
    PRIVATE
        cmptr_pos
        basefold_raa
        sha3
        pthread
        m
)

# Optimized Consensus Demo
add_executable(optimized_consensus_demo optimized_consensus_demo.c)
target_compile_definitions(optimized_consensus_demo PRIVATE _GNU_SOURCE)
target_link_libraries(optimized_consensus_demo
    PRIVATE
        cmptr_pos
        cmptr_accumulator
        cmptr_blockchain
        basefold_raa
        sha3
        common
        pthread
        m
)

# Comprehensive Benchmark
add_executable(comprehensive_benchmark comprehensive_benchmark.c)
target_compile_definitions(comprehensive_benchmark PRIVATE _GNU_SOURCE)
target_link_libraries(comprehensive_benchmark
    PRIVATE
        cmptr_pos
        cmptr_accumulator
        cmptr_blockchain
        basefold_raa
        sha3
        common
        pthread
        m
)

# Benchmark Analyzer
add_executable(benchmark_analyzer benchmark_analyzer.c)
target_compile_definitions(benchmark_analyzer PRIVATE _GNU_SOURCE)
target_link_libraries(benchmark_analyzer
    PRIVATE
        cmptr_pos
        cmptr_accumulator
        cmptr_blockchain
        basefold_raa
        sha3
        common
        pthread
        m
)

# Install
install(TARGETS pos_demo pos_validator_demo pos_sha3_only_demo pos_v2_complete_demo recursive_committee_demo instant_sync_demo proof_trigger_demo streaming_vrf_demo optimized_consensus_demo comprehensive_benchmark benchmark_analyzer
    DESTINATION bin
)