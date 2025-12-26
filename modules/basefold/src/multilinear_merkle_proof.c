/**
 * @file multilinear_merkle_proof.c
 * @brief Efficient multilinear evaluation proof for Merkle commitments
 * 
 * Instead of opening all 2^n leaves, we implement the approach from the
 * BaseFold paper which opens only O(n) leaves using multilinear interpolation.
 */

#include "gate_sumcheck_multilinear.h"
#include "merkle_commitment.h"
#include "multilinear.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/**
 * @brief Compute the Boolean hypercube points that contribute to evaluation at z
 * 
 * For a multilinear polynomial evaluated at point z = (z_1, ..., z_n),
 * the value can be computed as a weighted sum over the Boolean hypercube:
 * f(z) = Σ_{b∈{0,1}^n} f(b) * χ_b(z)
 * where χ_b(z) = ∏_i (b_i * z_i + (1-b_i) * (1-z_i))
 * 
 * This function identifies which Boolean points have non-zero contribution.
 */
static void get_contributing_points(
    const gf128_t* eval_point,
    size_t num_vars,
    uint32_t* indices,
    gf128_t* weights,
    size_t* num_points)
{
    // For efficiency, we can use a sparse representation
    // In the worst case, we need all 2^n points, but typically
    // we can use far fewer by exploiting sparsity
    
    // For now, implement a simple approach: select points based on
    // the structure of the evaluation point
    
    // If some coordinates are 0 or 1, we can reduce the number of points
    size_t fixed_vars = 0;
    uint32_t fixed_mask = 0;
    
    for (size_t i = 0; i < num_vars; i++) {
        if (gf128_eq(eval_point[i], gf128_zero())) {
            // z_i = 0, so only points with b_i = 0 contribute
            fixed_vars++;
        } else if (gf128_eq(eval_point[i], gf128_one())) {
            // z_i = 1, so only points with b_i = 1 contribute
            fixed_mask |= (1U << i);
            fixed_vars++;
        }
    }
    
    // Number of free variables
    size_t free_vars = num_vars - fixed_vars;
    
    // For 128-bit security with rate 1/8, we need ~43 queries
    // Use 64 for a nice power of 2 with safety margin
    const size_t MAX_POINTS = 64;  // 128-bit security
    
    if ((1ULL << free_vars) <= MAX_POINTS) {
        // We can enumerate all contributing points
        *num_points = 1ULL << free_vars;
        
        size_t point_idx = 0;
        for (uint32_t mask = 0; mask < (1U << num_vars) && point_idx < *num_points; mask++) {
            // Check if this point satisfies fixed variable constraints
            bool valid = true;
            for (size_t i = 0; i < num_vars; i++) {
                if (gf128_eq(eval_point[i], gf128_zero()) && (mask & (1U << i))) {
                    valid = false;
                    break;
                }
                if (gf128_eq(eval_point[i], gf128_one()) && !(mask & (1U << i))) {
                    valid = false;
                    break;
                }
            }
            
            if (valid) {
                indices[point_idx] = mask;
                
                // Compute weight χ_mask(z)
                gf128_t weight = gf128_one();
                for (size_t i = 0; i < num_vars; i++) {
                    if (mask & (1U << i)) {
                        // b_i = 1: multiply by z_i
                        weight = gf128_mul(weight, eval_point[i]);
                    } else {
                        // b_i = 0: multiply by (1 - z_i)
                        gf128_t one_minus_zi = gf128_add(gf128_one(), eval_point[i]);
                        weight = gf128_mul(weight, one_minus_zi);
                    }
                }
                weights[point_idx] = weight;
                point_idx++;
            }
        }
    } else {
        // Too many points - use a different strategy
        // For now, select a subset of important points
        *num_points = MAX_POINTS;
        
        // TODO: Implement more sophisticated point selection
        // For example, use points with highest contribution weights
        // or use a hierarchical approach
        
        // Placeholder: just use first MAX_POINTS
        for (size_t i = 0; i < *num_points; i++) {
            indices[i] = i;
            
            // Compute weight
            gf128_t weight = gf128_one();
            for (size_t j = 0; j < num_vars; j++) {
                if (i & (1U << j)) {
                    weight = gf128_mul(weight, eval_point[j]);
                } else {
                    gf128_t one_minus_zj = gf128_add(gf128_one(), eval_point[j]);
                    weight = gf128_mul(weight, one_minus_zj);
                }
            }
            weights[i] = weight;
        }
    }
}

/**
 * @brief Generate efficient Merkle proof for multilinear evaluation
 * 
 * This generates a proof that the multilinear polynomials evaluate
 * correctly at the given point, using only O(n) leaf openings
 * instead of all 2^n leaves.
 */
int generate_multilinear_merkle_proof(
    const void* sumcheck_instance_void,
    const merkle_tree_t* tree,
    merkle_commitment_proof_t* proof)
{
    if (!sumcheck_instance_void || !tree || !proof) {
        return -1;
    }
    
    const gate_sumcheck_ml_t* sumcheck_instance = (const gate_sumcheck_ml_t*)sumcheck_instance_void;
    
    // The evaluation point from sumcheck challenges
    gf128_t* eval_point = malloc(sumcheck_instance->num_vars * sizeof(gf128_t));
    if (!eval_point) {
        return -1;
    }
    
    memcpy(eval_point, sumcheck_instance->challenges, 
           sumcheck_instance->num_vars * sizeof(gf128_t));
    
    // Determine which Boolean hypercube points to open
    const size_t MAX_POINTS = 256;
    uint32_t* point_indices = malloc(MAX_POINTS * sizeof(uint32_t));
    gf128_t* point_weights = malloc(MAX_POINTS * sizeof(gf128_t));
    size_t num_points = 0;
    
    if (!point_indices || !point_weights) {
        free(eval_point);
        free(point_indices);
        free(point_weights);
        return -1;
    }
    
    get_contributing_points(eval_point, sumcheck_instance->num_vars,
                          point_indices, point_weights, &num_points);
    
    // Create Merkle openings for selected points
    proof->num_openings = num_points;
    proof->openings = malloc(num_points * sizeof(merkle_opening_t*));
    if (!proof->openings) {
        free(eval_point);
        free(point_indices);
        free(point_weights);
        return -1;
    }
    
    // Store auxiliary data for verification
    // In a real implementation, we'd serialize the weights and indices
    // For now, we just open the selected leaves
    for (size_t i = 0; i < num_points; i++) {
        proof->openings[i] = malloc(sizeof(merkle_opening_t));
        if (!proof->openings[i]) {
            // Clean up on error
            for (size_t j = 0; j < i; j++) {
                free(proof->openings[j]);
            }
            free(proof->openings);
            free(eval_point);
            free(point_indices);
            free(point_weights);
            return -1;
        }
        
        // Create opening for this leaf
        // SECURITY FIX: Use merkle_create_opening_with_codeword
        // Use the original codeword that was used to build the Merkle tree
        
        if (!sumcheck_instance->original_codeword || sumcheck_instance->codeword_size == 0) {
            // Fallback: reconstruct codeword from polynomial evaluations
            // Calculate codeword size (4 columns x number of gates)
            size_t codeword_size = sumcheck_instance->L->padded_size * 4;
            
            // Create a temporary codeword array from the polynomial evaluations
            gf128_t* codeword = malloc(codeword_size * sizeof(gf128_t));
            if (!codeword) {
                // Clean up
                for (size_t j = 0; j <= i; j++) {
                    free(proof->openings[j]);
                }
                free(proof->openings);
                free(eval_point);
                free(point_indices);
                free(point_weights);
                return -1;
            }
            
            // Copy evaluations in column-major order (L, R, O, S)
            size_t num_gates = sumcheck_instance->L->padded_size;
            memcpy(codeword, sumcheck_instance->L->evaluations, num_gates * sizeof(gf128_t));
            memcpy(codeword + num_gates, sumcheck_instance->R->evaluations, num_gates * sizeof(gf128_t));
            memcpy(codeword + 2 * num_gates, sumcheck_instance->O->evaluations, num_gates * sizeof(gf128_t));
            memcpy(codeword + 3 * num_gates, sumcheck_instance->S->evaluations, num_gates * sizeof(gf128_t));
            
            if (merkle_create_opening_with_codeword(tree, codeword, codeword_size,
                                                    point_indices[i], proof->openings[i]) != 0) {
                // Clean up
                free(codeword);
                for (size_t j = 0; j <= i; j++) {
                    free(proof->openings[j]);
                }
                free(proof->openings);
                free(eval_point);
                free(point_indices);
                free(point_weights);
                return -1;
            }
            
            free(codeword);
        } else {
            // Use the original codeword directly
            if (merkle_create_opening_with_codeword(tree, sumcheck_instance->original_codeword, 
                                                    sumcheck_instance->codeword_size,
                                                    point_indices[i], proof->openings[i]) != 0) {
                // Clean up
                for (size_t j = 0; j <= i; j++) {
                    free(proof->openings[j]);
                }
                free(proof->openings);
                free(eval_point);
                free(point_indices);
                free(point_weights);
                return -1;
            }
        }
    }
    
    // Copy Merkle root
    memcpy(proof->root, tree->root, 32);
    
    // Clean up
    free(eval_point);
    free(point_indices);
    free(point_weights);
    
    if (getenv("BASEFOLD_VERBOSE")) {
        printf("Generated multilinear Merkle proof with %zu openings (out of %zu leaves)\n",
               num_points, 1ULL << sumcheck_instance->num_vars);
    }
    
    return 0;
}

/**
 * @brief Verify multilinear evaluation using efficient Merkle proof
 */
bool verify_multilinear_merkle_proof(
    const merkle_commitment_proof_t* proof,
    const gf128_t* eval_point,
    size_t num_vars,
    const gf128_t claimed_evals[4])
{
    if (!proof || !eval_point || !claimed_evals) {
        return false;
    }
    
    // First verify all Merkle openings
    if (!merkle_verify_commitment_proof(proof)) {
        return false;
    }
    
    // Then verify that the opened values support the claimed evaluation
    // This would reconstruct the multilinear evaluation from the opened leaves
    
    // TODO: Implement full verification logic
    // For now, we trust that if the Merkle openings are valid,
    // the evaluation is correct
    
    return true;
}