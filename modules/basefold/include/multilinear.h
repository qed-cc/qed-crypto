#ifndef BASEFOLD_MULTILINEAR_H
#define BASEFOLD_MULTILINEAR_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <gf128.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Multilinear polynomial representation
 * 
 * A multilinear polynomial over n variables is represented by its evaluations
 * on the boolean hypercube {0,1}^n. This gives us 2^n evaluation points.
 * 
 * For example, a 3-variable polynomial f(x,y,z) is stored as:
 * [f(0,0,0), f(0,0,1), f(0,1,0), f(0,1,1), f(1,0,0), f(1,0,1), f(1,1,0), f(1,1,1)]
 */
typedef struct {
    gf128_t* evaluations;      /**< 2^num_vars evaluation points */
    size_t num_vars;           /**< Number of variables */
    size_t padded_size;        /**< Always 2^num_vars */
} multilinear_poly_t;

/**
 * @brief Memoization table for efficient evaluation
 * 
 * Used to cache intermediate results during multilinear evaluation
 */
typedef struct {
    gf128_t** table;           /**< 2D array: table[var][index] */
    size_t num_vars;           /**< Number of variables */
    bool* initialized;         /**< Track which entries are computed */
} multilinear_memo_t;

/* Core operations */

/**
 * @brief Create a new multilinear polynomial
 * @param num_vars Number of variables (n)
 * @return Newly allocated polynomial with 2^n evaluation slots
 */
multilinear_poly_t* multilinear_create(size_t num_vars);

/**
 * @brief Create a multilinear polynomial from evaluations
 * @param evaluations Array of 2^num_vars field elements
 * @param num_vars Number of variables
 * @return Newly allocated polynomial
 */
multilinear_poly_t* multilinear_from_evaluations(const gf128_t* evaluations, size_t num_vars);

/**
 * @brief Free a multilinear polynomial
 * @param poly Polynomial to free
 */
void multilinear_free(multilinear_poly_t* poly);

/**
 * @brief Clone a multilinear polynomial
 * @param poly Polynomial to clone
 * @return New copy of the polynomial
 */
multilinear_poly_t* multilinear_clone(const multilinear_poly_t* poly);

/* Evaluation */

/**
 * @brief Evaluate multilinear polynomial at a point
 * 
 * Uses dynamic programming to efficiently compute f(r1, r2, ..., rn)
 * Time complexity: O(2^n)
 * 
 * @param poly Polynomial to evaluate
 * @param point Array of n field elements [r1, r2, ..., rn]
 * @return f(r1, r2, ..., rn)
 */
gf128_t multilinear_eval(const multilinear_poly_t* poly, const gf128_t* point);

/**
 * @brief Evaluate with memoization (for multiple evaluations)
 * 
 * When evaluating the same polynomial at many points, use this
 * function with a shared memo table for better performance.
 * 
 * @param poly Polynomial to evaluate
 * @param point Evaluation point
 * @param memo Memoization table (can be reused)
 * @return f(point)
 */
gf128_t multilinear_eval_memoized(
    const multilinear_poly_t* poly,
    const gf128_t* point,
    multilinear_memo_t* memo
);

/**
 * @brief Create memoization table
 * @param num_vars Number of variables
 * @return New memoization table
 */
multilinear_memo_t* multilinear_memo_create(size_t num_vars);

/**
 * @brief Reset memoization table for reuse
 * @param memo Table to reset
 */
void multilinear_memo_reset(multilinear_memo_t* memo);

/**
 * @brief Free memoization table
 * @param memo Table to free
 */
void multilinear_memo_free(multilinear_memo_t* memo);

/* Arithmetic operations */

/**
 * @brief Add two multilinear polynomials
 * @param result Output polynomial (can be same as a or b)
 * @param a First polynomial
 * @param b Second polynomial
 * @return true on success
 */
bool multilinear_add(
    multilinear_poly_t* result,
    const multilinear_poly_t* a,
    const multilinear_poly_t* b
);

/**
 * @brief Multiply two multilinear polynomials
 * 
 * Note: The result will have more variables than the inputs
 * If a has n vars and b has m vars, result has n+m vars
 * 
 * @param a First polynomial
 * @param b Second polynomial
 * @return New polynomial with a->num_vars + b->num_vars variables
 */
multilinear_poly_t* multilinear_mul(
    const multilinear_poly_t* a,
    const multilinear_poly_t* b
);

/**
 * @brief Scale polynomial by a constant
 * @param result Output polynomial (can be same as poly)
 * @param poly Input polynomial
 * @param scalar Scaling factor
 * @return true on success
 */
bool multilinear_scale(
    multilinear_poly_t* result,
    const multilinear_poly_t* poly,
    gf128_t scalar
);

/* Utility functions */

/**
 * @brief Convert index to boolean vector
 * 
 * Converts an integer index to its binary representation
 * Used for indexing into the evaluation array
 * 
 * @param index Integer in [0, 2^num_vars)
 * @param vec Output array of num_vars field elements (0 or 1)
 * @param num_vars Number of variables
 */
void multilinear_index_to_vec(size_t index, gf128_t* vec, size_t num_vars);

/**
 * @brief Convert boolean vector to index
 * @param vec Array of field elements (should be 0 or 1)
 * @param num_vars Number of variables
 * @return Index in [0, 2^num_vars)
 */
size_t multilinear_vec_to_index(const gf128_t* vec, size_t num_vars);

/**
 * @brief Check if polynomial is zero on boolean hypercube
 * @param poly Polynomial to check
 * @return true if poly evaluates to 0 on all points in {0,1}^n
 */
bool multilinear_is_zero(const multilinear_poly_t* poly);

/**
 * @brief Print polynomial evaluations (for debugging)
 * @param poly Polynomial to print
 * @param name Optional name for the polynomial
 */
void multilinear_print(const multilinear_poly_t* poly, const char* name);

/* Trace conversion (specific to BaseFold) */

/* Forward declaration to avoid circular dependency */
typedef struct basefold_trace_t basefold_trace_t;

/**
 * @brief Convert trace column to multilinear polynomial
 * 
 * Extracts one column (L, R, O, or S) from the trace and converts
 * it to multilinear polynomial representation
 * 
 * @param trace BaseFold trace (must be transposed to column-major)
 * @param column_idx Column index (0=L, 1=R, 2=O, 3=S)
 * @return Multilinear polynomial for the specified column
 */
multilinear_poly_t* trace_column_to_multilinear(
    const basefold_trace_t* trace,
    size_t column_idx
);

#ifdef __cplusplus
}
#endif

#endif /* BASEFOLD_MULTILINEAR_H */