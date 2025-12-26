#ifndef BASEFOLD_VANISHING_POLY_H
#define BASEFOLD_VANISHING_POLY_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <gf128.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Vanishing polynomial for boolean hypercube
 * 
 * For the boolean hypercube {0,1}^n, the vanishing polynomial is:
 * v_H(x1,...,xn) = ∏(xi² - xi) = ∏xi(xi - 1)
 * 
 * This polynomial evaluates to 0 on all points in {0,1}^n
 * and is non-zero elsewhere.
 */
typedef struct {
    size_t num_vars;  /**< Number of variables n */
    /* No need to store coefficients - we evaluate on demand */
} vanishing_poly_t;

/**
 * @brief Create vanishing polynomial for boolean hypercube
 * @param num_vars Number of variables n
 * @return New vanishing polynomial
 */
vanishing_poly_t* vanishing_poly_create(size_t num_vars);

/**
 * @brief Free vanishing polynomial
 * @param v Polynomial to free
 */
void vanishing_poly_free(vanishing_poly_t* v);

/**
 * @brief Evaluate v_H at a point
 * 
 * Computes ∏xi(xi - 1) for all variables
 * 
 * @param v Vanishing polynomial
 * @param point Array of n field elements
 * @return v_H(point)
 */
gf128_t vanishing_hypercube_eval(
    const vanishing_poly_t* v,
    const gf128_t* point
);

/**
 * @brief Check if a point is on the boolean hypercube
 * 
 * Returns true if all coordinates are 0 or 1
 * 
 * @param point Array of field elements
 * @param num_vars Number of variables
 * @return true if point ∈ {0,1}^n
 */
bool is_boolean_point(const gf128_t* point, size_t num_vars);

/**
 * @brief Streaming evaluation of v_H(X) * r(X)
 * 
 * For zero-knowledge, we need to evaluate v_H(X) * r(X) where
 * r(X) is a random polynomial. This function does it without
 * materializing the full polynomial.
 * 
 * @param v Vanishing polynomial
 * @param point Evaluation point
 * @param seed PRG seed for generating r(X) coefficients
 * @param degree Degree bound for r(X)
 * @return v_H(point) * r(point)
 */
gf128_t vanishing_times_random_eval(
    const vanishing_poly_t* v,
    const gf128_t* point,
    const uint8_t seed[16],
    size_t degree
);

/**
 * @brief Compute degree of vanishing polynomial
 * 
 * For boolean hypercube, degree(v_H) = 2^n
 * 
 * @param num_vars Number of variables
 * @return Degree of v_H
 */
static inline size_t vanishing_poly_degree(size_t num_vars) {
    return num_vars;  // Each factor (xi² - xi) has degree 2, but for multilinear it's different
}

#ifdef __cplusplus
}
#endif

#endif /* BASEFOLD_VANISHING_POLY_H */