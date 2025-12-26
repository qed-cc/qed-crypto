#ifndef POLYNOMIAL_GF128_H
#define POLYNOMIAL_GF128_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <sys/types.h>  // For ssize_t
#include "gf128.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Polynomial over GF(2^128)
 * 
 * Represents a polynomial with coefficients in GF(2^128).
 * Coefficients are stored in order: a_0, a_1, ..., a_d
 * where the polynomial is a_0 + a_1*X + ... + a_d*X^d
 */
typedef struct {
    gf128_t* coeffs;      /**< Array of coefficients */
    size_t degree;        /**< Degree of polynomial (highest non-zero power) */
    size_t capacity;      /**< Allocated size of coeffs array */
} poly_gf128_t;

/**
 * @brief Evaluation domain for polynomial operations
 * 
 * Represents a multiplicative subgroup of GF(2^128)* used for
 * efficient polynomial evaluation via FFT/NTT.
 */
typedef struct {
    size_t size;          /**< Size of domain (must be power of 2) */
    gf128_t generator;    /**< Generator of multiplicative subgroup */
    gf128_t* elements;    /**< Precomputed domain elements */
    gf128_t* inv_elements; /**< Precomputed inverse elements for iFFT */
} eval_domain_t;

/* Polynomial creation and destruction */

/**
 * @brief Create a new polynomial with given capacity
 * @param capacity Initial capacity for coefficients
 * @return Newly allocated polynomial or NULL on failure
 */
poly_gf128_t* poly_new(size_t capacity);

/**
 * @brief Create polynomial from coefficients
 * @param coeffs Array of coefficients
 * @param num_coeffs Number of coefficients
 * @return Newly allocated polynomial or NULL on failure
 */
poly_gf128_t* poly_from_coeffs(const gf128_t* coeffs, size_t num_coeffs);

/**
 * @brief Create a zero polynomial
 * @return Newly allocated zero polynomial
 */
poly_gf128_t* poly_zero(void);

/**
 * @brief Create a constant polynomial
 * @param c Constant value
 * @return Newly allocated constant polynomial
 */
poly_gf128_t* poly_const(gf128_t c);

/**
 * @brief Clone a polynomial
 * @param p Polynomial to clone
 * @return Newly allocated copy of polynomial
 */
poly_gf128_t* poly_clone(const poly_gf128_t* p);

/**
 * @brief Free polynomial and its resources
 * @param p Polynomial to free
 */
void poly_free(poly_gf128_t* p);

/* Polynomial arithmetic */

/**
 * @brief Add two polynomials: result = a + b
 * @param result Output polynomial (can be same as a or b)
 * @param a First polynomial
 * @param b Second polynomial
 * @return true on success, false on failure
 */
bool poly_add(poly_gf128_t* result, const poly_gf128_t* a, const poly_gf128_t* b);

/**
 * @brief Subtract two polynomials: result = a - b
 * Note: In GF(2^128), subtraction is same as addition
 * @param result Output polynomial (can be same as a or b)
 * @param a First polynomial
 * @param b Second polynomial
 * @return true on success, false on failure
 */
static inline bool poly_sub(poly_gf128_t* result, const poly_gf128_t* a, const poly_gf128_t* b) {
    return poly_add(result, a, b);  // In characteristic 2, add = sub
}

/**
 * @brief Multiply two polynomials: result = a * b
 * @param result Output polynomial (must be different from a and b)
 * @param a First polynomial
 * @param b Second polynomial
 * @return true on success, false on failure
 */
bool poly_mul(poly_gf128_t* result, const poly_gf128_t* a, const poly_gf128_t* b);

/**
 * @brief Multiply polynomial by scalar: result = c * p
 * @param result Output polynomial (can be same as p)
 * @param c Scalar in GF(2^128)
 * @param p Polynomial
 * @return true on success, false on failure
 */
bool poly_scalar_mul(poly_gf128_t* result, gf128_t c, const poly_gf128_t* p);

/**
 * @brief Divide polynomials: dividend = divisor * quotient + remainder
 * @param quotient Output quotient polynomial (can be NULL if not needed)
 * @param remainder Output remainder polynomial (can be NULL if not needed)
 * @param dividend Dividend polynomial
 * @param divisor Divisor polynomial (must be non-zero)
 * @return true on success, false on failure
 */
bool poly_div(poly_gf128_t* quotient, poly_gf128_t* remainder,
              const poly_gf128_t* dividend, const poly_gf128_t* divisor);

/* Polynomial evaluation */

/**
 * @brief Evaluate polynomial at a point
 * @param p Polynomial
 * @param x Point at which to evaluate
 * @return p(x)
 */
gf128_t poly_eval(const poly_gf128_t* p, gf128_t x);

/**
 * @brief Evaluate polynomial at multiple points
 * @param p Polynomial
 * @param points Array of evaluation points
 * @param values Output array for values (must have space for num_points elements)
 * @param num_points Number of points
 * @return true on success, false on failure
 */
bool poly_multi_eval(const poly_gf128_t* p, const gf128_t* points,
                     gf128_t* values, size_t num_points);

/* Polynomial interpolation */

/**
 * @brief Lagrange interpolation from point-value pairs
 * @param points Array of x-coordinates (must be distinct)
 * @param values Array of y-coordinates
 * @param num_points Number of point-value pairs
 * @return Interpolated polynomial or NULL on failure
 */
poly_gf128_t* poly_interpolate(const gf128_t* points, const gf128_t* values,
                               size_t num_points);

/* Evaluation domain operations */

/**
 * @brief Create evaluation domain of given size
 * @param size Size of domain (must be power of 2)
 * @return Newly allocated domain or NULL on failure
 */
eval_domain_t* domain_new(size_t size);

/**
 * @brief Free evaluation domain
 * @param domain Domain to free
 */
void domain_free(eval_domain_t* domain);

/**
 * @brief Evaluate polynomial on entire domain using FFT
 * @param domain Evaluation domain
 * @param p Polynomial to evaluate
 * @param values Output array (must have space for domain->size elements)
 * @return true on success, false on failure
 */
bool domain_fft(const eval_domain_t* domain, const poly_gf128_t* p,
                gf128_t* values);

/**
 * @brief Interpolate polynomial from evaluations using inverse FFT
 * @param domain Evaluation domain
 * @param values Array of evaluations on domain
 * @param p Output polynomial
 * @return true on success, false on failure
 */
bool domain_ifft(const eval_domain_t* domain, const gf128_t* values,
                 poly_gf128_t* p);

/* Vanishing polynomial operations */

/**
 * @brief Compute vanishing polynomial for domain
 * @param domain Evaluation domain
 * @return Vanishing polynomial v_H(X) or NULL on failure
 */
poly_gf128_t* compute_vanishing_polynomial(const eval_domain_t* domain);

/**
 * @brief Evaluate vanishing polynomial at a point
 * @param domain Evaluation domain
 * @param x Point at which to evaluate
 * @return v_H(x)
 */
gf128_t vanishing_poly_eval(const eval_domain_t* domain, gf128_t x);

/**
 * @brief Check if polynomial vanishes on domain
 * @param domain Evaluation domain
 * @param p Polynomial to check
 * @return true if p(h) = 0 for all h in domain
 */
bool poly_vanishes_on_domain(const eval_domain_t* domain, const poly_gf128_t* p);

/* Utility functions */

/**
 * @brief Get degree of polynomial
 * @param p Polynomial
 * @return Degree of polynomial (-1 for zero polynomial)
 */
static inline ssize_t poly_degree(const poly_gf128_t* p) {
    return p ? (ssize_t)p->degree : -1;
}

/**
 * @brief Check if polynomial is zero
 * @param p Polynomial
 * @return true if polynomial is zero
 */
bool poly_is_zero(const poly_gf128_t* p);

/**
 * @brief Print polynomial for debugging
 * @param p Polynomial
 * @param name Name to display
 */
void poly_print(const poly_gf128_t* p, const char* name);

#ifdef __cplusplus
}
#endif

#endif // POLYNOMIAL_GF128_H