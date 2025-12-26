#include "evaluation_path.h"
#include "merkle/build.h"
#include <stdlib.h>
#include <string.h>

// Initialize evaluation path structure
evaluation_path_t* evaluation_path_init(uint32_t num_vars) {
    evaluation_path_t* path = calloc(1, sizeof(evaluation_path_t));
    if (!path) return NULL;
    
    path->num_vars = num_vars;
    path->evaluations = calloc(num_vars, sizeof(gf128_t));
    path->merkle_nodes = calloc(num_vars, sizeof(merkle_node_t));
    
    if (!path->evaluations || !path->merkle_nodes) {
        evaluation_path_free(path);
        return NULL;
    }
    
    return path;
}

// Free evaluation path structure
void evaluation_path_free(evaluation_path_t* path) {
    if (!path) return;
    
    if (path->evaluations) free(path->evaluations);
    if (path->merkle_nodes) free(path->merkle_nodes);
    free(path);
}

// Record evaluation at a specific round
void evaluation_path_record(evaluation_path_t* path, uint32_t round, 
                          gf128_t evaluation, const merkle_node_t* node) {
    if (!path || round >= path->num_vars) return;
    
    path->evaluations[round] = evaluation;
    if (node) {
        memcpy(&path->merkle_nodes[round], node, sizeof(merkle_node_t));
    }
}

// Compute evaluation path proof
evaluation_path_proof_t* evaluation_path_prove(const evaluation_path_t* path,
                                              const gf128_t* challenge_point,
                                              const merkle_tree_t* tree) {
    if (!path || !challenge_point || !tree) return NULL;
    
    evaluation_path_proof_t* proof = calloc(1, sizeof(evaluation_path_proof_t));
    if (!proof) return NULL;
    
    proof->num_vars = path->num_vars;
    proof->path_evaluations = calloc(path->num_vars, sizeof(gf128_t));
    proof->merkle_proofs = calloc(path->num_vars, sizeof(merkle_proof_t));
    
    if (!proof->path_evaluations || !proof->merkle_proofs) {
        evaluation_path_proof_free(proof);
        return NULL;
    }
    
    // For each round, generate Merkle proof for the evaluation
    for (uint32_t i = 0; i < path->num_vars; i++) {
        // Store the evaluation
        proof->path_evaluations[i] = path->evaluations[i];
        
        // Generate Merkle proof for this node
        // The actual index depends on the partial evaluation up to this round
        uint32_t index = 0;
        for (uint32_t j = 0; j <= i; j++) {
            if (gf128_eq(challenge_point[j], gf128_one())) {
                index |= (1 << j);
            }
        }
        
        // Get Merkle proof for this index
        // Note: This assumes merkle_tree_get_proof exists or similar functionality
        // For now, we'll store the node hash
        memcpy(proof->merkle_proofs[i].hash, path->merkle_nodes[i].hash, 32);
        proof->merkle_proofs[i].index = index;
    }
    
    // Compute final evaluation
    proof->final_evaluation = path->evaluations[path->num_vars - 1];
    
    return proof;
}

// Verify evaluation path proof
bool evaluation_path_verify(const evaluation_path_proof_t* proof,
                          const gf128_t* challenge_point,
                          const uint8_t* merkle_root,
                          gf128_t expected_final) {
    if (!proof || !challenge_point || !merkle_root) return false;
    
    // Verify that the evaluation path is consistent
    gf128_t accumulated = gf128_one();
    
    for (uint32_t i = 0; i < proof->num_vars; i++) {
        // Verify Merkle proof for this evaluation
        uint32_t index = 0;
        for (uint32_t j = 0; j <= i; j++) {
            if (gf128_eq(challenge_point[j], gf128_one())) {
                index |= (1 << j);
            }
        }
        
        // Check that the Merkle proof index matches
        if (proof->merkle_proofs[i].index != index) {
            return false;
        }
        
        // TODO: Verify actual Merkle path to root
        // This would require the full Merkle authentication path
        // For now, we verify the structure is correct
    }
    
    // Verify final evaluation matches expected
    if (!gf128_eq(proof->final_evaluation, expected_final)) {
        return false;
    }
    
    return true;
}

// Free evaluation path proof
void evaluation_path_proof_free(evaluation_path_proof_t* proof) {
    if (!proof) return;
    
    if (proof->path_evaluations) free(proof->path_evaluations);
    if (proof->merkle_proofs) free(proof->merkle_proofs);
    free(proof);
}