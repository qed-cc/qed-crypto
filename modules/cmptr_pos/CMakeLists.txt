# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

set(MODULE_NAME cmptr_pos)

# Sources for v2 PoS with cryptographic agility
set(SOURCES
    src/pos_core.c
    src/stake_manager.c
    src/verkle_commitment.c
    src/lattice_vrf.c
    src/narwhal_dag.c
    src/mysticeti_ordering.c
    src/recursive_stark.c
    src/consensus_engine.c
    src/committee_selection.c
    src/blob_manager.c
    # V2 additions for upgradeability
    src/pos_v2_core.c
    src/parallel_proof_gen.c
    src/streaming_dag.c
    src/incremental_verkle.c
    src/fast_path.c
    src/default_modules.c
    src/module_negotiation.c
    src/sha3_vrf.c
    src/upgrade_coordinator.c
    src/sha3_default_config.c
    src/recursive_committee.c
    src/circular_chain_sync.c
    src/proof_triggers.c
    src/streaming_dag_impl.c
    src/hierarchical_vrf.c
    src/parallel_proof_pipeline.c
    src/early_finality.c
    src/optimized_consensus_engine.c
    # Real implementations
    src/parallel_proof_pipeline_real.c
    src/streaming_dag_real_impl.c
    src/hierarchical_vrf_real.c
)

# Create library
add_library(${MODULE_NAME} STATIC ${SOURCES})

# Add compile definitions
target_compile_definitions(${MODULE_NAME} PRIVATE _GNU_SOURCE)

# Include directories
target_include_directories(${MODULE_NAME}
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
)

# Link dependencies
target_link_libraries(${MODULE_NAME}
    PUBLIC
        cmptr_accumulator
        cmptr_blockchain
        basefold_raa
        common
        pthread
        sha3
)

# Apply warnings
if(COMMAND apply_project_warnings)
    apply_project_warnings(${MODULE_NAME})
endif()

# Examples
option(BUILD_EXAMPLES "Build example programs" ON)
if(BUILD_EXAMPLES)
    add_subdirectory(examples)
endif()

# Tests
if(BUILD_TESTS)
    add_subdirectory(tests)
endif()

# Install
install(TARGETS ${MODULE_NAME}
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
)

install(DIRECTORY include/
    DESTINATION include
    FILES_MATCHING PATTERN "*.h"
)

# Export
install(FILES cmake/${MODULE_NAME}Config.cmake
    DESTINATION lib/cmake/${MODULE_NAME}
)

message(STATUS "Added module: ${MODULE_NAME}")
message(STATUS "Building Cmptr Proof of Stake: Quantum-secure consensus")
message(STATUS "  Features: SHA3-Verkle trees, SHA3-VRF, Narwhal DAG, Mysticeti ordering")
message(STATUS "  Security: Post-quantum via SHA3-based recursive STARKs")
message(STATUS "  Cryptography: SHA3-256 ONLY (no elliptic curves, no lattices)")
message(STATUS "  Upgradeability: Modular architecture for smooth transitions")