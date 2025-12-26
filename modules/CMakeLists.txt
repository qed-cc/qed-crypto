# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Main modules CMakeLists.txt
# This file manages all modules, including git submodules

# Include the common compiler warnings configuration
include(${CMAKE_SOURCE_DIR}/cmake/CompilerWarnings.cmake)

# Function to add a module with standard configuration
function(add_gate_module MODULE_NAME)
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${MODULE_NAME}/CMakeLists.txt")
        add_subdirectory(${MODULE_NAME})
        message(STATUS "Added module: ${MODULE_NAME}")
        
        # Enable coverage for module if in Coverage build
        if(CMAKE_BUILD_TYPE STREQUAL "Coverage")
            # Module targets will inherit coverage flags from parent
            message(STATUS "  Coverage enabled for ${MODULE_NAME}")
        endif()
    else()
        message(WARNING "Module directory ${MODULE_NAME} exists but has no CMakeLists.txt")
    endif()
endfunction()

# Example of adding a built-in module
# Uncomment and modify as needed
# add_gate_module(core)

# Add the common utilities module (required for secure random)
add_gate_module(common)

# Add the SHA3 module (required for BaseFold)
add_gate_module(sha3)

# Add the GF128 module
add_gate_module(gf128)

# Circuit modules removed - these were empty placeholders

# REMOVED: Groth16 is NOT post-quantum secure
# Gate Computer uses ONLY BaseFold RAA for post-quantum security

# Circuit engine module (requires circuit_io) is not needed for cmptr; skip
# add_gate_module(circuit_engine)

# BaseFold RAA hybrid proof system
option(BUILD_BASEFOLD_RAA "Build BaseFold RAA hybrid (optimized BaseFold with RAA encoding)" ON)
if(BUILD_BASEFOLD_RAA)
    add_gate_module(basefold_raa)
    message(STATUS "Building BaseFold RAA module: Optimized proofs with RAA encoding")
    message(STATUS "  Target: ~40KB proofs with ~150ms generation time")
    message(STATUS "  Full 128-bit post-quantum security")
endif()

# Add truth verifier module
add_gate_module(truth_verifier)

# Add assertion verifier module (SHA3-based verification chain)
add_gate_module(assertion_verifier)

# Add formal proof circuits module
option(BUILD_FORMAL_PROOF_CIRCUITS "Build formal proof circuits module" ON)
if(BUILD_FORMAL_PROOF_CIRCUITS)
    add_gate_module(formal_proof_circuits)
endif()
# Add cmptr accumulator module - Revolutionary scalable blockchain accumulator
option(BUILD_CMPTR_ACCUMULATOR "Build CMPTR Accumulator module for 1M TPS blockchain" ON)
if(BUILD_CMPTR_ACCUMULATOR)
    add_gate_module(cmptr_accumulator)
    message(STATUS "Building CMPTR Accumulator: Recursive proof accumulators with PoW")
    message(STATUS "  Features: PARKED/ACTIVE tokens, auto-pruning, 1M TPS")
endif()

# Add cmptr blockchain module - Hierarchical blockchain with bounded storage
option(BUILD_CMPTR_BLOCKCHAIN "Build CMPTR Blockchain module with hierarchical architecture" ON)
if(BUILD_CMPTR_BLOCKCHAIN)
    add_gate_module(cmptr_blockchain)
    message(STATUS "Building CMPTR Blockchain: Hierarchical blockchain with 1M TPS")
    message(STATUS "  Node types: Aggregator, Generator, Producer, Validator")
    message(STATUS "  Storage tiers: Archive, Full, Light, Ultra-Light")
endif()

# Add cmptr PoS module - Quantum-secure Proof of Stake consensus
option(BUILD_CMPTR_POS "Build CMPTR Proof of Stake module with recursive STARKs" ON)
if(BUILD_CMPTR_POS)
    add_gate_module(cmptr_pos)
    message(STATUS "Building CMPTR PoS: Quantum-secure Proof of Stake consensus")
    message(STATUS "  Features: Verkle trees, Lattice VRF, Narwhal DAG, Mysticeti ordering")
    message(STATUS "  Security: Post-quantum via recursive STARKs")
endif()

# Add Cmptr Signatures module - Post-quantum aggregatable signatures
option(BUILD_CMPTR_SIGNATURES "Build Cmptr Signatures module" ON)
if(BUILD_CMPTR_SIGNATURES)
    add_gate_module(cmptr_signatures)
    message(STATUS "Building Cmptr Signatures: Post-quantum aggregatable signatures with STARKs")
    message(STATUS "  Features: Constant-size aggregated signatures via recursive composition")
    message(STATUS "  Use case: Aggregate 100+ signatures into one 190KB proof")
endif()

# Add Cmptr Stream module - Ultra-low latency encryption
option(BUILD_CMPTR_STREAM "Build Cmptr Stream cipher module" ON)
if(BUILD_CMPTR_STREAM)
    add_gate_module(cmptr_stream)
    message(STATUS "Building Cmptr Stream: Ultra-low latency quantum-secure encryption")
    message(STATUS "  Features: < 1μs latency, 10+ Gbps throughput, SHA3-only")
    message(STATUS "  Use case: Real-time communication, video streaming, gaming")
endif()

# Add Cmptr Channel module - Authenticated encryption with forward secrecy
option(BUILD_CMPTR_CHANNEL "Build Cmptr Channel module" ON)
if(BUILD_CMPTR_CHANNEL)
    add_gate_module(cmptr_channel)
    message(STATUS "Building Cmptr Channel: Authenticated encryption with forward secrecy")
    message(STATUS "  Features: < 10μs RTT, hash ratcheting, tampering detection")
    message(STATUS "  Use case: Secure communication channels, client-server, P2P")
endif()

# Add Cmptr Exchange module - STARK-based key agreement
option(BUILD_CMPTR_EXCHANGE "Build Cmptr Exchange module" ON)
if(BUILD_CMPTR_EXCHANGE)
    add_gate_module(cmptr_exchange)
    message(STATUS "Building Cmptr Exchange: STARK-based key exchange without number theory")
    message(STATUS "  Features: Commit-reveal protocol, zero-knowledge, authenticated")
    message(STATUS "  Use case: Quantum-secure key agreement, TLS replacement")
endif()

# Add Cmptr VRF module - Verifiable Random Functions
option(BUILD_CMPTR_VRF "Build Cmptr VRF module" ON)
if(BUILD_CMPTR_VRF)
    add_gate_module(cmptr_vrf)
    message(STATUS "Building Cmptr VRF: Verifiable Random Functions without elliptic curves")
    message(STATUS "  Features: SHA3-based, deterministic randomness, STARK proofs")
    message(STATUS "  Use case: Consensus leader election, lottery systems, randomness beacons")
endif()

# Add Cmptr Trees module - Optimized Merkle Trees
option(BUILD_CMPTR_TREES "Build Cmptr Trees module" ON)
if(BUILD_CMPTR_TREES)
    add_gate_module(cmptr_trees)
    message(STATUS "Building Cmptr Trees: Cache-optimized Merkle trees with AVX-512")
    message(STATUS "  Features: 8-way parallel hashing, batch operations, sparse trees")
    message(STATUS "  Use case: State commitments, light clients, efficient proofs")
endif()

# Add Cmptr Commitments module - Vector Commitments
option(BUILD_CMPTR_COMMITMENTS "Build Cmptr Commitments module" ON)
if(BUILD_CMPTR_COMMITMENTS)
    add_gate_module(cmptr_commitments)
    message(STATUS "Building Cmptr Commitments: Vector commitments with constant-size proofs")
    message(STATUS "  Features: Commit to N values → 32 bytes, updateable proofs")
    message(STATUS "  Use case: Stateless clients, rollups, compressed state proofs")
endif()

# Detect and add remaining module directories (excluding those already added)
set(ALREADY_ADDED_MODULES "common" "sha3" "gf128" "core" "basefold_verifier" "blaze" "basefold_raa" "truth_verifier" "assertion_verifier" "formal_proof_circuits" "cmptr_accumulator" "cmptr_blockchain" "cmptr_pos" "cmptr_signatures" "cmptr_stream" "cmptr_channel" "cmptr_exchange" "cmptr_vrf" "cmptr_trees" "cmptr_commitments" "semantic_qa") # List of modules already added manually
file(GLOB MODULE_DIRS RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_CURRENT_SOURCE_DIR}/*)
foreach(MODULE_DIR ${MODULE_DIRS})
    list(FIND ALREADY_ADDED_MODULES ${MODULE_DIR} MODULE_INDEX)
    if(MODULE_INDEX EQUAL -1 AND 
       IS_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/${MODULE_DIR} AND 
       NOT ${MODULE_DIR} STREQUAL "CMakeFiles" AND
       EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${MODULE_DIR}/CMakeLists.txt")
        add_gate_module(${MODULE_DIR})
    endif()
endforeach()

# Note: To add a git submodule, use:
# git submodule add https://github.com/username/repo.git modules/module_name
# Then run:
# git submodule update --init --recursive