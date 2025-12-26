/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

# Circular Recursion Implementation Status

## Overview
We are implementing circular recursion for blockchain proofs, where each proof recursively verifies the entire chain history from genesis. This is tracked by truth buckets T700-T702 and F600.

## Key Discovery: Sumcheck on Constraint Polynomials

### The Problem
The BaseFold RAA prover was running sumcheck directly on the witness values, but the verifier expected consistency between rounds that wasn't satisfied. The issue: `proof->claimed_eval` (set to `current[0]` after all reductions) didn't match the first round's `g0 + g1`.

### The Solution
We discovered that sumcheck should run on the **constraint polynomial** F(L,R,O,S), not the witness directly:
- Gate constraint: `F(L,R,O,S) = S*(L*R - O) + (1-S)*(L + R - O)`
- In GF(2^128): `F(L,R,O,S) = S*(L*R + O) + (1+S)*(L + R + O)`
- Valid gate constraints produce F = 0
- The constraint polynomial sums to zero over the hypercube

## Implementation Progress

### ✅ Completed (40%)
1. **Gate Witness Generator** (`gate_witness_generator.c`)
   - Proper 4-column format: L (left), R (right), O (output), S (selector)
   - Functions for XOR gates, AND gates, multi-gate circuits
   - Constraint verification

2. **Constraint Polynomial** (`constraint_polynomial.c`)
   - Computes F(L,R,O,S) from witness
   - Verifies sum over hypercube is zero
   - Tested with standalone examples

3. **Fixed Sumcheck** (modified `basefold_raa_prove.c`)
   - Now computes constraint polynomial first
   - Runs sumcheck on constraint (not witness)
   - Proper initialization and consistency

4. **Testing Infrastructure**
   - `sumcheck_witness_debug.c` - Analyzes witness structure
   - `test_constraint_standalone.c` - Verifies constraint approach
   - `circular_recursion_progress.c` - Tracks implementation status

### ⚠️ In Progress (10%)
5. **Binary NTT Conversion**
   - Issue: After sumcheck on constraint polynomial, we need univariate coefficients
   - The transition from multilinear sumcheck to univariate representation
   - Compilation errors in basefold module (AES intrinsics)

### ❌ TODO (50%)
6. **RAA Encoding** - Reed-Solomon encode the univariate coefficients
7. **Merkle Tree Commitment** - SHA3-based commitment to RAA codeword
8. **SHA3 State Transition Circuit** - Circuit for blockchain state updates
9. **Recursive Verifier Circuit** - 5.4M gate circuit for proof verification
10. **End-to-End Integration** - Complete circular recursion

## Files Created/Modified

### New Files
- `/modules/basefold_raa/src/gate_witness_generator.c`
- `/modules/basefold_raa/include/gate_witness_generator.h`
- `/modules/basefold_raa/src/constraint_polynomial.c`
- `/modules/basefold_raa/include/constraint_polynomial.h`
- `/tools/sumcheck_witness_debug.c`
- `/tools/test_constraint_standalone.c`
- `/tools/circular_recursion_progress.c`

### Modified Files
- `/modules/basefold_raa/src/basefold_raa_prove.c` - Uses constraint polynomial
- `/modules/basefold_raa/CMakeLists.txt` - Added new sources
- `/examples/CMakeLists.txt` - Added circular blockchain examples

## Truth Bucket Status
- **T600-T603**: Recursive proofs work ✓ (179ms achieved)
- **T700**: Circular recursion defined ✓
- **T701**: Requires 5.4M gate verifier ✓ 
- **T702**: Generates valid proofs ⚠️ (40% complete)
- **F600**: Currently FALSE/UNCERTAIN → Will be TRUE when T702 passes

## Next Steps
1. Fix Binary NTT compilation/linking issues
2. Complete the witness→univariate coefficient conversion
3. Implement RAA encoding with proper parameters
4. Add Merkle tree commitment layer
5. Create SHA3 state transition circuit
6. Integrate recursive verifier circuit
7. Test end-to-end circular recursion

## Key Insight
The breakthrough was understanding that BaseFold's sumcheck protocol operates on constraint polynomials that encode the validity of gate evaluations, not on the witness values directly. This ensures the polynomial sums to zero over the hypercube, which is what the sumcheck protocol expects.