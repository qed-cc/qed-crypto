/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0 */

#include "../include/basefold_integration.h"
#include "../include/gate_types.h"
#include "../../sha3/include/sha3.h"
#include <stdlib.h>
#include <string.h>
#include <assert.h>

// Extended gate types for formal proofs
typedef enum {
    GATE_TYPE_AND = 0,
    GATE_TYPE_XOR = 1,
    GATE_TYPE_MUL = 2,      // For arithmetic constraints
    GATE_TYPE_ADD = 3,      // For arithmetic constraints
    GATE_TYPE_CUSTOM = 4,   // For complex logical operations
    GATE_TYPE_INVALID = 255
} extended_gate_type_t;

/**
 * @brief Convert logical gate to arithmetic constraint
 * 
 * Maps boolean operations to arithmetic over GF(2^128):
 * - AND: a * b
 * - OR: a + b - a*b
 * - NOT: 1 - a
 * - XOR: a + b - 2*a*b
 * - IMPLIES: 1 - a + a*b
 * - IFF: 1 - a - b + 2*a*b
 */
static int convert_gate_to_constraint(int gate_type, 
                                     const gf128_t* inputs,
                                     gf128_t* output) {
    gf128_t one, two, tmp1, tmp2;
    gf128_from_int(&one, 1);
    gf128_from_int(&two, 2);
    
    switch(gate_type) {
        case GATE_AND:
            gf128_mul(output, &inputs[0], &inputs[1]);
            break;
            
        case GATE_OR:
            // a + b - a*b
            gf128_add(output, &inputs[0], &inputs[1]);
            gf128_mul(&tmp1, &inputs[0], &inputs[1]);
            gf128_sub(output, output, &tmp1);
            break;
            
        case GATE_NOT:
            // 1 - a
            gf128_sub(output, &one, &inputs[0]);
            break;
            
        case GATE_XOR:
            // a + b - 2*a*b
            gf128_add(output, &inputs[0], &inputs[1]);
            gf128_mul(&tmp1, &inputs[0], &inputs[1]);
            gf128_mul(&tmp2, &two, &tmp1);
            gf128_sub(output, output, &tmp2);
            break;
            
        case GATE_IMPLIES:
            // 1 - a + a*b
            gf128_sub(output, &one, &inputs[0]);
            gf128_mul(&tmp1, &inputs[0], &inputs[1]);
            gf128_add(output, output, &tmp1);
            break;
            
        case GATE_IFF:
            // 1 - a - b + 2*a*b
            gf128_sub(output, &one, &inputs[0]);
            gf128_sub(output, output, &inputs[1]);
            gf128_mul(&tmp1, &inputs[0], &inputs[1]);
            gf128_mul(&tmp2, &two, &tmp1);
            gf128_add(output, output, &tmp2);
            break;
            
        default:
            return -1; // Unsupported gate type
    }
    
    return 0;
}

int convert_to_gate_circuit(const proof_circuit_t* proof_circuit,
                           circuit_t* circuit) {
    if (!proof_circuit || !circuit) {
        return -1;
    }
    
    // Create evaluator circuit
    circuit_t* eval_circuit = evaluator_init_circuit(
        proof_circuit->num_inputs,
        proof_circuit->num_gates,
        proof_circuit->num_outputs
    );
    
    if (!eval_circuit) {
        return -1;
    }
    
    // Convert each gate - we'll expand complex gates into AND/XOR combinations
    int gates_added = 0;
    
    for (int i = 0; i < proof_circuit->num_gates; i++) {
        wire_id_t input1 = proof_circuit->gate_inputs[i][0] + 2; // +2 for constants 0,1
        wire_id_t input2 = (proof_circuit->gate_type[i] != GATE_NOT) ? 
                          proof_circuit->gate_inputs[i][1] + 2 : 0;
        wire_id_t output = proof_circuit->gate_output[i] + 2;
        
        switch(proof_circuit->gate_type[i]) {
            case GATE_AND:
                evaluator_add_gate(eval_circuit, GATE_AND, input1, input2, output);
                gates_added++;
                break;
                
            case GATE_XOR:
                evaluator_add_gate(eval_circuit, GATE_XOR, input1, input2, output);
                gates_added++;
                break;
                
            case GATE_NOT:
                // NOT(a) = XOR(a, 1)
                evaluator_add_gate(eval_circuit, GATE_XOR, input1, 1, output);
                gates_added++;
                break;
                
            case GATE_OR:
                // OR(a,b) = XOR(AND(a,b), XOR(a,b))
                // Need intermediate wires
                wire_id_t and_out = proof_circuit->num_wires + 2 + i*2;
                wire_id_t xor_out = proof_circuit->num_wires + 2 + i*2 + 1;
                
                evaluator_add_gate(eval_circuit, GATE_AND, input1, input2, and_out);
                evaluator_add_gate(eval_circuit, GATE_XOR, input1, input2, xor_out);
                evaluator_add_gate(eval_circuit, GATE_XOR, and_out, xor_out, output);
                gates_added += 3;
                break;
                
            default:
                // Complex gates need more sophisticated decomposition
                // For now, we'll handle them in the GF(2^128) evaluation
                break;
        }
    }
    
    // Set output wires - constraints that must equal 1
    wire_id_t* output_wires = calloc(proof_circuit->num_constraints, sizeof(wire_id_t));
    for (int i = 0; i < proof_circuit->num_constraints; i++) {
        output_wires[i] = proof_circuit->constraint_wires[i] + 2;
    }
    evaluator_set_outputs(eval_circuit, output_wires, proof_circuit->num_constraints);
    free(output_wires);
    
    // Prepare circuit for evaluation
    evaluator_prepare_circuit(eval_circuit);
    
    *circuit = *eval_circuit;
    free(eval_circuit); // Just free the struct, not the internal arrays
    
    return 0;
}

int convert_witness_to_gf128(const proof_circuit_t* proof_circuit,
                            const uint8_t* logical_witness,
                            gf128_t* gf_witness,
                            size_t witness_size) {
    if (!proof_circuit || !logical_witness || !gf_witness) {
        return -1;
    }
    
    // Convert boolean values to GF(2^128)
    for (size_t i = 0; i < witness_size; i++) {
        gf128_from_int(&gf_witness[i], logical_witness[i] ? 1 : 0);
    }
    
    return 0;
}

int generate_basefold_proof(const proof_circuit_t* proof_circuit,
                           const uint8_t* logical_witness,
                           int enable_zk,
                           uint8_t** proof_out,
                           size_t* proof_size_out) {
    if (!proof_circuit || !proof_out || !proof_size_out) {
        return -1;
    }
    
    // Per Axiom A002: Zero-knowledge is MANDATORY
    if (!enable_zk) {
        return -1; // Violation of fundamental axiom
    }
    
    // Convert circuit to gate format
    circuit_t circuit;
    memset(&circuit, 0, sizeof(circuit));
    
    int ret = convert_to_gate_circuit(proof_circuit, &circuit);
    if (ret < 0) {
        return ret;
    }
    
    // Determine witness size (power of 2)
    size_t witness_size = 1;
    size_t num_variables = 0;
    while (witness_size < proof_circuit->num_wires) {
        witness_size <<= 1;
        num_variables++;
    }
    
    // Allocate GF(2^128) witness
    gf128_t* gf_witness = calloc(witness_size, sizeof(gf128_t));
    if (!gf_witness) {
        ret = -1;
        goto cleanup;
    }
    
    // Generate witness if not provided
    uint8_t* witness_to_use = (uint8_t*)logical_witness;
    uint8_t* generated_witness = NULL;
    
    if (!logical_witness) {
        // Need to generate witness for existential statements
        witness_config_t config;
        get_default_witness_config(&config);
        
        generated_witness = calloc(proof_circuit->num_wires, sizeof(uint8_t));
        if (!generated_witness) {
            ret = -1;
            goto cleanup;
        }
        
        ret = generate_existential_witness(proof_circuit, &config, generated_witness);
        if (ret < 0) {
            goto cleanup;
        }
        
        witness_to_use = generated_witness;
    }
    
    // Convert witness to GF(2^128)
    ret = convert_witness_to_gf128(proof_circuit, witness_to_use, 
                                   gf_witness, proof_circuit->num_wires);
    if (ret < 0) {
        goto cleanup;
    }
    
    // Create wire state and evaluate circuit
    wire_state_t* wire_state = evaluator_init_wire_state(&circuit);
    if (!wire_state) {
        ret = -1;
        goto cleanup;
    }
    
    // Set inputs from witness
    evaluator_set_inputs(wire_state, witness_to_use, proof_circuit->num_inputs);
    
    // Evaluate circuit
    if (!evaluator_evaluate_circuit(&circuit, wire_state)) {
        evaluator_free_wire_state(wire_state);
        ret = -1;
        goto cleanup;
    }
    
    // Convert wire values to GF(2^128) witness
    for (size_t i = 0; i < wire_state->num_wires && i < witness_size; i++) {
        gf128_from_int(&gf_witness[i], wire_state->values[i] ? 1 : 0);
    }
    
    // Verify constraints are satisfied (outputs should all be 1)
    uint8_t* outputs = calloc(circuit.num_outputs, sizeof(uint8_t));
    evaluator_get_outputs(&circuit, wire_state, outputs);
    
    for (uint32_t i = 0; i < circuit.num_outputs; i++) {
        if (outputs[i] != 1) {
            free(outputs);
            evaluator_free_wire_state(wire_state);
            ret = -1; // Constraint not satisfied
            goto cleanup;
        }
    }
    
    free(outputs);
    evaluator_free_wire_state(wire_state);
    
    // Configure BaseFold RAA
    basefold_raa_config_t config = {
        .num_variables = num_variables,
        .security_level = BASEFOLD_RAA_SECURITY_BITS,
        .enable_zk = 1,  // Always enabled per Axiom A002
        .num_threads = 0 // Auto-detect
    };
    
    // Generate proof
    basefold_raa_proof_t proof;
    memset(&proof, 0, sizeof(proof));
    
    ret = basefold_raa_prove(gf_witness, &config, &proof);
    if (ret < 0) {
        goto cleanup;
    }
    
    // Serialize proof
    size_t estimated_size = basefold_raa_proof_size(&config);
    uint8_t* proof_buffer = malloc(estimated_size);
    if (!proof_buffer) {
        basefold_raa_proof_free(&proof);
        ret = -1;
        goto cleanup;
    }
    
    ssize_t actual_size = serialize_basefold_proof(&proof, proof_buffer, estimated_size);
    if (actual_size < 0) {
        free(proof_buffer);
        basefold_raa_proof_free(&proof);
        ret = -1;
        goto cleanup;
    }
    
    *proof_out = proof_buffer;
    *proof_size_out = actual_size;
    
    basefold_raa_proof_free(&proof);
    ret = 0;
    
cleanup:
    if (generated_witness) {
        free(generated_witness);
    }
    if (gf_witness) {
        free(gf_witness);
    }
    // Free circuit arrays
    for (int i = 0; i < circuit.num_gates; i++) {
        free(circuit.gates[i].inputs);
    }
    free(circuit.gates);
    free(circuit.constraint_wires);
    
    return ret;
}

int verify_basefold_proof(const proof_circuit_t* proof_circuit,
                         const uint8_t* proof,
                         size_t proof_size) {
    if (!proof_circuit || !proof || proof_size == 0) {
        return -1;
    }
    
    // Deserialize proof
    basefold_raa_proof_t raa_proof;
    memset(&raa_proof, 0, sizeof(raa_proof));
    
    int ret = deserialize_basefold_proof(proof, proof_size, &raa_proof);
    if (ret < 0) {
        return ret;
    }
    
    // Determine number of variables
    size_t witness_size = 1;
    size_t num_variables = 0;
    while (witness_size < proof_circuit->num_wires) {
        witness_size <<= 1;
        num_variables++;
    }
    
    // Configure verifier
    basefold_raa_config_t config = {
        .num_variables = num_variables,
        .security_level = BASEFOLD_RAA_SECURITY_BITS,
        .enable_zk = 1,  // Always enabled
        .num_threads = 0
    };
    
    // Verify proof
    ret = basefold_raa_verify(&raa_proof, &config);
    
    basefold_raa_proof_free(&raa_proof);
    return ret;
}

size_t estimate_proof_size(const proof_circuit_t* proof_circuit) {
    if (!proof_circuit) {
        return 0;
    }
    
    // Determine number of variables
    size_t witness_size = 1;
    size_t num_variables = 0;
    while (witness_size < proof_circuit->num_wires) {
        witness_size <<= 1;
        num_variables++;
    }
    
    basefold_raa_config_t config = {
        .num_variables = num_variables,
        .security_level = BASEFOLD_RAA_SECURITY_BITS,
        .enable_zk = 1,
        .num_threads = 0
    };
    
    return basefold_raa_proof_size(&config);
}

ssize_t serialize_basefold_proof(const basefold_raa_proof_t* proof,
                                uint8_t* buffer,
                                size_t buffer_size) {
    if (!proof || !buffer || buffer_size == 0) {
        return -1;
    }
    
    size_t offset = 0;
    
    // Write proof tag
    if (offset + 32 > buffer_size) return -1;
    memcpy(buffer + offset, proof->proof_tag, 32);
    offset += 32;
    
    // Write metadata
    if (offset + sizeof(size_t) * 4 > buffer_size) return -1;
    memcpy(buffer + offset, &proof->num_sumcheck_rounds, sizeof(size_t));
    offset += sizeof(size_t);
    memcpy(buffer + offset, &proof->witness_size, sizeof(size_t));
    offset += sizeof(size_t);
    memcpy(buffer + offset, &proof->num_queries, sizeof(size_t));
    offset += sizeof(size_t);
    memcpy(buffer + offset, &proof->randomizer_degree, sizeof(size_t));
    offset += sizeof(size_t);
    
    // Write sumcheck commitments
    size_t sumcheck_size = proof->num_sumcheck_rounds * 32;
    if (offset + sumcheck_size > buffer_size) return -1;
    memcpy(buffer + offset, proof->sumcheck_commitments, sumcheck_size);
    offset += sumcheck_size;
    
    // Write sumcheck responses
    size_t response_size = proof->num_sumcheck_rounds * sizeof(gf128_t);
    if (offset + response_size > buffer_size) return -1;
    memcpy(buffer + offset, proof->sumcheck_responses, response_size);
    offset += response_size;
    
    // Write RAA root
    if (offset + 32 > buffer_size) return -1;
    memcpy(buffer + offset, proof->raa_root, 32);
    offset += 32;
    
    // Write claimed evaluation
    if (offset + sizeof(gf128_t) > buffer_size) return -1;
    memcpy(buffer + offset, &proof->claimed_eval, sizeof(gf128_t));
    offset += sizeof(gf128_t);
    
    // Write query data
    for (size_t i = 0; i < proof->num_queries; i++) {
        // Query index
        if (offset + sizeof(size_t) > buffer_size) return -1;
        memcpy(buffer + offset, &proof->query_indices[i], sizeof(size_t));
        offset += sizeof(size_t);
        
        // Query value
        if (offset + sizeof(gf128_t) > buffer_size) return -1;
        memcpy(buffer + offset, &proof->query_values[i], sizeof(gf128_t));
        offset += sizeof(gf128_t);
        
        // Leaf values (8 per leaf for Merkle tree)
        if (offset + 8 * sizeof(gf128_t) > buffer_size) return -1;
        memcpy(buffer + offset, proof->query_leaf_values[i], 8 * sizeof(gf128_t));
        offset += 8 * sizeof(gf128_t);
        
        // Merkle path (log2(codeword_size) * 32 bytes)
        size_t path_len = 0;
        size_t cs = proof->raa_codeword_size / 8; // 8 values per leaf
        while (cs > 1) {
            cs >>= 1;
            path_len++;
        }
        
        if (offset + path_len * 32 > buffer_size) return -1;
        for (size_t j = 0; j < path_len; j++) {
            memcpy(buffer + offset, proof->merkle_paths[i][j], 32);
            offset += 32;
        }
    }
    
    // Write ZK data
    size_t zk_size = proof->randomizer_degree * sizeof(gf128_t);
    if (offset + zk_size > buffer_size) return -1;
    memcpy(buffer + offset, proof->randomizer_coeffs, zk_size);
    offset += zk_size;
    
    if (offset + 32 > buffer_size) return -1;
    memcpy(buffer + offset, proof->mask_seed, 32);
    offset += 32;
    
    return offset;
}

int deserialize_basefold_proof(const uint8_t* buffer,
                              size_t buffer_size,
                              basefold_raa_proof_t* proof) {
    if (!buffer || !proof || buffer_size < 32) {
        return -1;
    }
    
    memset(proof, 0, sizeof(*proof));
    size_t offset = 0;
    
    // Read proof tag
    memcpy(proof->proof_tag, buffer + offset, 32);
    offset += 32;
    
    // Read metadata
    if (offset + sizeof(size_t) * 4 > buffer_size) return -1;
    memcpy(&proof->num_sumcheck_rounds, buffer + offset, sizeof(size_t));
    offset += sizeof(size_t);
    memcpy(&proof->witness_size, buffer + offset, sizeof(size_t));
    offset += sizeof(size_t);
    memcpy(&proof->num_queries, buffer + offset, sizeof(size_t));
    offset += sizeof(size_t);
    memcpy(&proof->randomizer_degree, buffer + offset, sizeof(size_t));
    offset += sizeof(size_t);
    
    // Allocate and read sumcheck commitments
    size_t sumcheck_size = proof->num_sumcheck_rounds * 32;
    proof->sumcheck_commitments = malloc(sumcheck_size);
    if (!proof->sumcheck_commitments) return -1;
    
    if (offset + sumcheck_size > buffer_size) {
        basefold_raa_proof_free(proof);
        return -1;
    }
    memcpy(proof->sumcheck_commitments, buffer + offset, sumcheck_size);
    offset += sumcheck_size;
    
    // Allocate and read sumcheck responses
    size_t response_size = proof->num_sumcheck_rounds * sizeof(gf128_t);
    proof->sumcheck_responses = malloc(response_size);
    if (!proof->sumcheck_responses) {
        basefold_raa_proof_free(proof);
        return -1;
    }
    
    if (offset + response_size > buffer_size) {
        basefold_raa_proof_free(proof);
        return -1;
    }
    memcpy(proof->sumcheck_responses, buffer + offset, response_size);
    offset += response_size;
    
    // Read RAA root
    if (offset + 32 > buffer_size) {
        basefold_raa_proof_free(proof);
        return -1;
    }
    memcpy(proof->raa_root, buffer + offset, 32);
    offset += 32;
    
    // Read claimed evaluation
    if (offset + sizeof(gf128_t) > buffer_size) {
        basefold_raa_proof_free(proof);
        return -1;
    }
    memcpy(&proof->claimed_eval, buffer + offset, sizeof(gf128_t));
    offset += sizeof(gf128_t);
    
    // Calculate codeword size from witness size
    proof->raa_codeword_size = proof->witness_size * BASEFOLD_RAA_REPETITION_FACTOR;
    
    // Allocate query arrays
    proof->query_indices = calloc(proof->num_queries, sizeof(size_t));
    proof->query_values = calloc(proof->num_queries, sizeof(gf128_t));
    proof->query_leaf_values = calloc(proof->num_queries, sizeof(gf128_t*));
    proof->merkle_paths = calloc(proof->num_queries, sizeof(uint8_t**));
    
    if (!proof->query_indices || !proof->query_values || 
        !proof->query_leaf_values || !proof->merkle_paths) {
        basefold_raa_proof_free(proof);
        return -1;
    }
    
    // Read query data
    for (size_t i = 0; i < proof->num_queries; i++) {
        // Query index
        if (offset + sizeof(size_t) > buffer_size) {
            basefold_raa_proof_free(proof);
            return -1;
        }
        memcpy(&proof->query_indices[i], buffer + offset, sizeof(size_t));
        offset += sizeof(size_t);
        
        // Query value
        if (offset + sizeof(gf128_t) > buffer_size) {
            basefold_raa_proof_free(proof);
            return -1;
        }
        memcpy(&proof->query_values[i], buffer + offset, sizeof(gf128_t));
        offset += sizeof(gf128_t);
        
        // Leaf values
        proof->query_leaf_values[i] = malloc(8 * sizeof(gf128_t));
        if (!proof->query_leaf_values[i]) {
            basefold_raa_proof_free(proof);
            return -1;
        }
        
        if (offset + 8 * sizeof(gf128_t) > buffer_size) {
            basefold_raa_proof_free(proof);
            return -1;
        }
        memcpy(proof->query_leaf_values[i], buffer + offset, 8 * sizeof(gf128_t));
        offset += 8 * sizeof(gf128_t);
        
        // Merkle path
        size_t path_len = 0;
        size_t cs = proof->raa_codeword_size / 8;
        while (cs > 1) {
            cs >>= 1;
            path_len++;
        }
        
        proof->merkle_paths[i] = calloc(path_len, sizeof(uint8_t*));
        if (!proof->merkle_paths[i]) {
            basefold_raa_proof_free(proof);
            return -1;
        }
        
        for (size_t j = 0; j < path_len; j++) {
            proof->merkle_paths[i][j] = malloc(32);
            if (!proof->merkle_paths[i][j]) {
                basefold_raa_proof_free(proof);
                return -1;
            }
            
            if (offset + 32 > buffer_size) {
                basefold_raa_proof_free(proof);
                return -1;
            }
            memcpy(proof->merkle_paths[i][j], buffer + offset, 32);
            offset += 32;
        }
    }
    
    // Read ZK data
    size_t zk_size = proof->randomizer_degree * sizeof(gf128_t);
    proof->randomizer_coeffs = malloc(zk_size);
    if (!proof->randomizer_coeffs) {
        basefold_raa_proof_free(proof);
        return -1;
    }
    
    if (offset + zk_size > buffer_size) {
        basefold_raa_proof_free(proof);
        return -1;
    }
    memcpy(proof->randomizer_coeffs, buffer + offset, zk_size);
    offset += zk_size;
    
    if (offset + 32 > buffer_size) {
        basefold_raa_proof_free(proof);
        return -1;
    }
    memcpy(proof->mask_seed, buffer + offset, 32);
    
    return 0;
}

void get_default_witness_config(witness_config_t* config) {
    if (config) {
        config->max_iterations = 1000000;
        config->use_random_search = 1;
        config->num_threads = 0; // Auto-detect
        config->timeout_ms = 60000; // 60 seconds
    }
}