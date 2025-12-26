/**
 * @file merkle_sumcheck_binding.h
 * @brief CRITICAL SECURITY FIX: Merkle-SumCheck binding verification
 * 
 * This header declares functions that verify the binding between
 * Merkle tree commitments and sumcheck protocol final scalars.
 * Without this verification, the proof system is completely unsound.
 */

#ifndef MERKLE_SUMCHECK_BINDING_H
#define MERKLE_SUMCHECK_BINDING_H

#include <stdbool.h>
#include <stddef.h>
#include "gf128.h"
#include "merkle_commitment.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Verify that Merkle-committed values bind to sumcheck final scalar
 * 
 * This is the main entry point for verifying the critical binding between
 * the Merkle tree commitment and the sumcheck protocol. It handles both
 * boolean and non-boolean evaluation points.
 * 
 * For boolean points: Directly verifies that the opened leaf evaluates to final_scalar
 * For non-boolean points: Performs multilinear interpolation on hypercube neighbors
 * 
 * @param merkle_proof The Merkle opening proof with leaf values
 * @param eval_point The evaluation point from sumcheck
 * @param num_vars Number of variables (log2 of number of gates)
 * @param final_scalar The claimed final scalar from sumcheck
 * @param is_gates true for gate sumcheck, false for wiring sumcheck
 * @return 0 on successful verification, -1 on failure
 */
int verify_merkle_sumcheck_binding(
    const merkle_commitment_proof_t* merkle_proof,
    const gf128_t* eval_point,
    size_t num_vars,
    gf128_t final_scalar,
    bool is_gates
);

/**
 * @brief Verify binding for boolean evaluation points
 * 
 * When the evaluation point is in {0,1}^n, we can directly check
 * that the opened Merkle leaf values evaluate to the claimed scalar.
 * 
 * @param merkle_proof The Merkle opening proof
 * @param eval_point Boolean evaluation point
 * @param num_vars Number of variables
 * @param final_scalar The claimed final scalar
 * @param is_gates true for gate sumcheck, false for wiring
 * @return 0 on success, -1 on failure
 */
int verify_merkle_sumcheck_binding_boolean(
    const merkle_commitment_proof_t* merkle_proof,
    const gf128_t* eval_point,
    size_t num_vars,
    gf128_t final_scalar,
    bool is_gates
);

/**
 * @brief Verify binding for non-boolean evaluation points
 * 
 * When the evaluation point has non-binary coordinates, we must:
 * 1. Open multiple Merkle leaves (hypercube corners)
 * 2. Perform multilinear interpolation
 * 3. Verify the interpolated value matches the claimed scalar
 * 
 * @param merkle_proof The Merkle opening proof (must contain all needed corners)
 * @param eval_point Non-boolean evaluation point
 * @param num_vars Number of variables
 * @param final_scalar The claimed final scalar
 * @param is_gates true for gate sumcheck, false for wiring
 * @return 0 on success, -1 on failure
 */
int verify_merkle_sumcheck_binding_interpolated(
    const merkle_commitment_proof_t* merkle_proof,
    const gf128_t* eval_point,
    size_t num_vars,
    gf128_t final_scalar,
    bool is_gates
);

#ifdef __cplusplus
}
#endif

#endif /* MERKLE_SUMCHECK_BINDING_H */