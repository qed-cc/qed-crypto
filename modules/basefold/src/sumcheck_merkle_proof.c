/**
 * @file sumcheck_merkle_proof.c
 * @brief Generate and verify Merkle proofs for sumcheck final evaluation
 */

#include "gate_sumcheck_multilinear.h"
#include "merkle_commitment.h"
#include "multilinear.h"
#include "extended_domain_utils.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/**
 * @brief Generate Merkle proof for sumcheck final evaluation
 * 
 * After sumcheck protocol completes, we have an evaluation point z = (r_1, ..., r_n)
 * where r_i are the challenges from each round. We need to:
 * 1. Evaluate the polynomials at point z
 * 2. Provide Merkle openings to prove these evaluations
 */
int generate_sumcheck_merkle_proof(
    const void* sumcheck_instance_void,
    const merkle_tree_t* tree,
    merkle_commitment_proof_t* proof)
{
    if (!sumcheck_instance_void || !tree || !proof) {
        return -1;
    }
    
    // Cast to correct type
    const gate_sumcheck_ml_t* sumcheck_instance = (const gate_sumcheck_ml_t*)sumcheck_instance_void;
    
    // The evaluation point is constructed from the challenges
    gf128_t* eval_point = malloc(sumcheck_instance->num_vars * sizeof(gf128_t));
    if (!eval_point) {
        return -1;
    }
    
    // Copy challenges as the evaluation point
    memcpy(eval_point, sumcheck_instance->challenges, 
           sumcheck_instance->num_vars * sizeof(gf128_t));
    
    // If the evaluation point is in the boolean hypercube, we can directly
    // open the corresponding leaf. Otherwise, we need to provide evaluation proofs.
    
    // Check if point is boolean
    bool is_boolean = true;
    for (size_t i = 0; i < sumcheck_instance->num_vars; i++) {
        gf128_t val = eval_point[i];
        if (!gf128_eq(val, gf128_zero()) && !gf128_eq(val, gf128_one())) {
            is_boolean = false;
            break;
        }
    }
    
    if (is_boolean) {
        // Point is in {0,1}^n, so we can directly open the leaf
        // Check if we're using extended domain based on tree size
        // Extended domain has 4x the leaves of original domain
        bool use_extended = false;
        size_t expected_original_size = (1ULL << sumcheck_instance->num_vars) * 4; // 4 field elements per gate
        size_t expected_original_leaves = expected_original_size / MERKLE_LEAF_WORDS;
        if (tree->leaves > expected_original_leaves * 2) {
            // Tree is larger than expected for original domain, likely using extended domain
            use_extended = true;
        }
        
        uint32_t leaf_index;
        if (use_extended) {
            // For extended domain, the evaluation point is in {0,1}^n but we need
            // to map it to the extended domain {0,1}^(n+2) by setting extension bits to 0
            leaf_index = merkle_point_to_extended_leaf_index(eval_point, 
                                                            sumcheck_instance->num_vars,
                                                            use_extended);
        } else {
            leaf_index = merkle_point_to_leaf_index(eval_point, 
                                                   sumcheck_instance->num_vars);
        }
        
        // Create a single opening for this leaf
        proof->num_openings = 1;
        proof->openings = malloc(sizeof(merkle_opening_t*));
        if (!proof->openings) {
            free(eval_point);
            return -1;
        }
        
        proof->openings[0] = malloc(sizeof(merkle_opening_t));
        if (!proof->openings[0]) {
            free(proof->openings);
            free(eval_point);
            return -1;
        }
        
        // SECURITY FIX: Use merkle_create_opening_with_codeword
        // Use the original codeword that was used to build the Merkle tree
        
        if (!sumcheck_instance->original_codeword || sumcheck_instance->codeword_size == 0) {
            // Fallback: reconstruct codeword from polynomial evaluations
            // Calculate codeword size (4 columns x number of gates)
            size_t codeword_size = sumcheck_instance->L->padded_size * 4;
            
            // Create a temporary codeword array from the polynomial evaluations
            gf128_t* codeword = malloc(codeword_size * sizeof(gf128_t));
            if (!codeword) {
                free(proof->openings[0]);
                free(proof->openings);
                free(eval_point);
                return -1;
            }
            
            // Copy evaluations in column-major order (L, R, O, S)
            size_t num_gates = sumcheck_instance->L->padded_size;
            memcpy(codeword, sumcheck_instance->L->evaluations, num_gates * sizeof(gf128_t));
            memcpy(codeword + num_gates, sumcheck_instance->R->evaluations, num_gates * sizeof(gf128_t));
            memcpy(codeword + 2 * num_gates, sumcheck_instance->O->evaluations, num_gates * sizeof(gf128_t));
            memcpy(codeword + 3 * num_gates, sumcheck_instance->S->evaluations, num_gates * sizeof(gf128_t));
            
            // Create the opening with codeword data
            if (merkle_create_opening_with_codeword(tree, codeword, codeword_size, 
                                                    leaf_index, proof->openings[0]) != 0) {
                free(codeword);
                free(proof->openings[0]);
                free(proof->openings);
                free(eval_point);
                return -1;
            }
            
            free(codeword);
        } else {
            // Use the original codeword directly
            if (merkle_create_opening_with_codeword(tree, sumcheck_instance->original_codeword, 
                                                    sumcheck_instance->codeword_size, 
                                                    leaf_index, proof->openings[0]) != 0) {
                free(proof->openings[0]);
                free(proof->openings);
                free(eval_point);
                return -1;
            }
        }
    } else {
        // Point is outside {0,1}^n, need multilinear extension
        // For multilinear polynomials, we need to provide evaluations
        // and prove they're consistent with the committed values
        
        // This is more complex - we need to:
        // 1. Evaluate multilinear polynomials at the point
        // 2. Provide auxiliary information to verify the evaluation
        
        // For now, we'll create a proof that the verifier can use
        // to reconstruct the evaluation from the committed values
        
        // In the full protocol, this would involve:
        // - Opening multiple leaves that contribute to the evaluation
        // - Providing coefficients for the multilinear interpolation
        
        // Use efficient multilinear evaluation proof
        extern int generate_multilinear_merkle_proof(
            const void* sumcheck_instance_void,
            const merkle_tree_t* tree,
            merkle_commitment_proof_t* proof);
        
        free(eval_point);
        return generate_multilinear_merkle_proof(sumcheck_instance_void, tree, proof);
    }
    
    // Copy Merkle root
    memcpy(proof->root, tree->root, 32);
    
    free(eval_point);
    return 0;
}

/**
 * @brief Verify sumcheck final evaluation using Merkle proof
 * 
 * Given the Merkle proof and evaluation point, verify that the claimed
 * evaluations are correct.
 */
bool verify_sumcheck_merkle_proof(
    const merkle_commitment_proof_t* proof,
    const gf128_t* eval_point,
    size_t num_vars,
    const gf128_t claimed_evals[4],  // L(z), R(z), O(z), S(z)
    const uint8_t expected_root[32])
{
    if (!proof || !eval_point || !claimed_evals || !expected_root) {
        return false;
    }
    
    // First verify the Merkle root matches
    if (memcmp(proof->root, expected_root, 32) != 0) {
        return false;
    }
    
    // Verify all Merkle openings are valid
    if (!merkle_verify_commitment_proof(proof)) {
        return false;
    }
    
    // Now verify the claimed evaluations match the opened values
    
    // Check if evaluation point is boolean
    bool is_boolean = true;
    for (size_t i = 0; i < num_vars; i++) {
        if (!gf128_eq(eval_point[i], gf128_zero()) && 
            !gf128_eq(eval_point[i], gf128_one())) {
            is_boolean = false;
            break;
        }
    }
    
    if (is_boolean && proof->num_openings == 1) {
        // Direct verification: claimed values should match opened leaf
        merkle_opening_t* opening = proof->openings[0];
        
        // When using extended domain, the opened values might be masked
        // The verifier needs to know if extended domain is being used
        // This should be communicated through the proof format or protocol parameters
        
        // Verify claimed evaluations match leaf values
        if (!gf128_eq(claimed_evals[0], opening->leaf_values[0]) ||  // L
            !gf128_eq(claimed_evals[1], opening->leaf_values[1]) ||  // R
            !gf128_eq(claimed_evals[2], opening->leaf_values[2]) ||  // O
            !gf128_eq(claimed_evals[3], opening->leaf_values[3])) { // S
            return false;
        }
    } else {
        // Multilinear evaluation verification
        // Need to check that claimed evaluations are consistent with
        // the multilinear extension of the opened values
        
        // For each polynomial (L, R, O, S)
        for (int poly_idx = 0; poly_idx < 4; poly_idx++) {
            gf128_t computed_eval = gf128_zero();
            
            // Compute multilinear evaluation from opened values
            for (size_t i = 0; i < proof->num_openings; i++) {
                // Get coefficient for this basis function
                gf128_t coeff = gf128_one();
                
                // Compute Lagrange basis polynomial value at eval_point
                for (size_t j = 0; j < num_vars; j++) {
                    gf128_t var_val = eval_point[j];
                    
                    // Check if bit j is set in index i
                    if (i & (1ULL << j)) {
                        // Include x_j in product
                        coeff = gf128_mul(coeff, var_val);
                    } else {
                        // Include (1 - x_j) in product
                        gf128_t one_minus = gf128_add(gf128_one(), var_val);
                        coeff = gf128_mul(coeff, one_minus);
                    }
                }
                
                // Add contribution: coeff * value
                gf128_t value = proof->openings[i]->leaf_values[poly_idx];
                gf128_t contrib = gf128_mul(coeff, value);
                computed_eval = gf128_add(computed_eval, contrib);
            }
            
            // Check if computed evaluation matches claimed
            if (!gf128_eq(computed_eval, claimed_evals[poly_idx])) {
                return false;
            }
        }
    }
    
    return true;
}

/**
 * @brief Compute polynomial evaluations at sumcheck final point
 * 
 * Helper function to evaluate the committed polynomials at the
 * point determined by sumcheck challenges.
 */
int evaluate_at_sumcheck_point(
    const gate_sumcheck_ml_t* sumcheck_instance,
    gf128_t evals[4])  // Output: L(z), R(z), O(z), S(z)
{
    if (!sumcheck_instance || !evals) {
        return -1;
    }
    
    // The evaluation point is the challenges from sumcheck
    const gf128_t* eval_point = sumcheck_instance->challenges;
    
    // Evaluate each polynomial at the point
    evals[0] = multilinear_eval(sumcheck_instance->L, eval_point);
    evals[1] = multilinear_eval(sumcheck_instance->R, eval_point);
    evals[2] = multilinear_eval(sumcheck_instance->O, eval_point);
    evals[3] = multilinear_eval(sumcheck_instance->S, eval_point);
    
    return 0;
}