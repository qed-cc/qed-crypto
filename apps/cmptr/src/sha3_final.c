#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <unistd.h>
#include <fcntl.h>
#include <evaluator.h>
#include "circuit_format.h"
// #include "circuit_io.h"
#include "input_validation.h"
#include "sha3_final.h"
#include "logger.h"

/**
 * @brief SHA3-256 Circuit Implementation
 * 
 * This implementation generates a circuit with exactly 192,086 gates for SHA3-256.
 * The gate count is composed of:
 * - 24 Keccak-f rounds
 * - Each round uses approximately 8,003 gates
 * - Total: 24 * 8,003 ≈ 192,086 gates
 */

/**
 * @brief Keccak-f[1600] rotation offsets for the rho step - from FIPS 202
 * 
 * R[x][y] contains the rotation offset for the lane at position (x,y)
 */
static const int R[5][5] = {
    {  0, 36,  3, 41, 18},
    {  1, 44, 10, 45,  2},
    { 62,  6, 43, 15, 61},
    { 28, 55, 25, 21, 56},
    { 27, 20, 39,  8, 14}
};

/**
 * @brief Keccak-f round constants for the iota step - from FIPS 202
 * 
 * These constants are XORed with the first lane (0,0) in each round
 */
static const uint64_t RC_native[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL,
    0x8000000080008000ULL, 0x000000000000808bULL, 0x0000000080000001ULL,
    0x8000000080008081ULL, 0x8000000000008009ULL, 0x000000000000008aULL,
    0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL,
    0x8000000000008003ULL, 0x8000000000008002ULL, 0x8000000000000080ULL,
    0x000000000000800aULL, 0x800000008000000aULL, 0x8000000080008081ULL,
    0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL
};

/**
 * @brief Get the user-visible input size for SHA3-256
 * 
 * This is the max size the user can provide before padding.
 * We reserve space for the domain separator (0x06 = 4 bits in MSB-first order)
 * and the end bit (0x80 = 1 bit at the end of the block).
 */
uint32_t sha3_get_user_input_size(sha3_type_t type) {
    (void)type; // Only SHA3-256 is supported
    return 1082; // 1088 - 4 - 2 (domain separator bits and end bit)
}

/**
 * @brief Get the input size for SHA3-256 (rate)
 * 
 * The rate is the portion of the state that is used for input absorption.
 * It's calculated as the state size (1600) minus the capacity (2 * output size).
 */
uint32_t sha3_get_input_size(sha3_type_t type) {
    (void)type; // Only SHA3-256 is supported
    return 1088; // 1600 - 2*256
}

/**
 * @brief Get the output size for SHA3-256
 */
uint32_t sha3_get_output_size(sha3_type_t type) {
    (void)type; // Only SHA3-256 is supported
    return 256;
}

/**
 * @brief Generate a SHA3-256 circuit
 * 
 * This function generates a gate circuit for SHA3-256 hash function.
 * The circuit takes up to 1088 input bits (the rate) and produces a 256-bit output.
 * The implementation follows the FIPS 202 standard with proper padding and bit ordering.
 * 
 * @param type SHA3 type (only SHA3-256 is supported)
 * @return Pointer to the generated circuit, or NULL on error
 */
circuit_t* generate_sha3_circuit(sha3_type_t type) {
    (void)type; // Only SHA3-256 is supported
    
    /* Allocate state A[x][y][z] */
    circuit_t* circuit = evaluator_init_circuit(2 + 1088, 1000000, 256);
    if (!circuit) {
        LOG_ERROR("sha3", "Failed to create circuit");
        return NULL;
    }

    uint32_t A[5][5][64];
    for (int x = 0; x < 5; x++) {
        for (int y = 0; y < 5; y++) {
            for (int z = 0; z < 64; z++) {
                if (5 * y + x < 17) {
                    /* rate lanes from inputs */
                    A[x][y][z] = 2 + (5 * y + x) * 64 + z;
                } else {
                    /* capacity lanes start at constant zero (index 0) */
                    A[x][y][z] = 0;
                }
            }
        }
    }

    uint32_t next = 2 + 1088;
    /* 24 rounds of Keccak-f[1600] */
    for (int rnd = 0; rnd < 24; rnd++) {
        /* θ step */
        uint32_t C_parity[5][64];
        uint32_t D_xor[5][64];
        
        // Compute column parities C[x,z]
        for (int x = 0; x < 5; x++) {
            for (int z = 0; z < 64; z++) {
                uint32_t t = A[x][0][z];
                for (int y = 1; y < 5; y++) {
                    uint32_t nw = next++;
                    evaluator_add_gate(circuit, GATE_XOR, t, A[x][y][z], nw);
                    t = nw;
                }
                C_parity[x][z] = t;
            }
        }

        // Compute D[x,z]
        for (int x = 0; x < 5; x++) {
            for (int z = 0; z < 64; z++) {
                uint32_t a1 = C_parity[(x + 4) % 5][z];
                uint32_t a2 = C_parity[(x + 1) % 5][(z + 63) % 64];
                uint32_t nw = next++;
                evaluator_add_gate(circuit, GATE_XOR, a1, a2, nw);
                D_xor[x][z] = nw;
            }
        }

        // Apply D to state
        for (int x = 0; x < 5; x++) {
            for (int y = 0; y < 5; y++) {
                for (int z = 0; z < 64; z++) {
                    uint32_t old = A[x][y][z];
                    uint32_t d = D_xor[x][z];
                    uint32_t nw = next++;
                    evaluator_add_gate(circuit, GATE_XOR, old, d, nw);
                    A[x][y][z] = nw;
                }
            }
        }

        /* ρ and π: wire mapping */
        uint32_t B[5][5][64];
        for (int x = 0; x < 5; x++) {
            for (int y = 0; y < 5; y++) {
                for (int z = 0; z < 64; z++) {
                    int newX = y;
                    int newY = (2 * x + 3 * y) % 5;
                    int newZ = (z + R[x][y]) % 64;
                    B[newX][newY][newZ] = A[x][y][z];
                }
            }
        }
        memcpy(A, B, sizeof(A));

        /* χ step */
        uint32_t Bchi[5][5][64];
        memcpy(Bchi, A, sizeof(A));

        /* NOT and AND/XOR in three layers */
        uint32_t not1[5][5][64];
        for (int x = 0; x < 5; x++) for (int y = 0; y < 5; y++) for (int z = 0; z < 64; z++) {
            uint32_t b1 = Bchi[(x + 1) % 5][y][z];
            uint32_t nw = next++;
            evaluator_add_gate(circuit, GATE_XOR, b1, 1, nw);
            not1[x][y][z] = nw;
        }
        
        uint32_t and1[5][5][64];
        for (int x = 0; x < 5; x++) for (int y = 0; y < 5; y++) for (int z = 0; z < 64; z++) {
            uint32_t nb = not1[x][y][z];
            uint32_t b2 = Bchi[(x + 2) % 5][y][z];
            uint32_t nw = next++;
            evaluator_add_gate(circuit, GATE_AND, nb, b2, nw);
            and1[x][y][z] = nw;
        }
        
        for (int x = 0; x < 5; x++) for (int y = 0; y < 5; y++) for (int z = 0; z < 64; z++) {
            uint32_t b0 = Bchi[x][y][z];
            uint32_t aw = and1[x][y][z];
            uint32_t nw = next++;
            evaluator_add_gate(circuit, GATE_XOR, b0, aw, nw);
            A[x][y][z] = nw;
        }

        /* ι step: inject round constant */
        for (int z = 0; z < 64; z++) {
            /* Flip bit-plane z if RC_native bit z is set */
            if ((RC_native[rnd] >> z) & 1) {
                uint32_t old = A[0][0][z];
                uint32_t nw = next++;
                evaluator_add_gate(circuit, GATE_XOR, old, 1, nw);
                A[0][0][z] = nw;
            }
        }
    }

    /* Collect first 256 output bits (lane 0-3, bitplanes 0-63) */
    // Collect 256-bit digest in SHA3-256 byte order: 32 bytes from first 4 lanes
    uint32_t out_bits[256];
    for (int byte = 0; byte < 32; byte++) {
        int lane = byte / 8;
        int x = lane % 5;
        int y = lane / 5;
        int base_z = (byte % 8) * 8;
        // Map bitplanes to output byte bits (MSB-first)
        for (int k = 0; k < 8; k++) {
            out_bits[byte * 8 + k] = A[x][y][base_z + (7 - k)];
        }
    }
    
    evaluator_set_outputs(circuit, out_bits, 256);
    evaluator_prepare_circuit(circuit);
    
    return circuit;
}

/**
 * @brief Evaluate the SHA3-256 circuit
 * 
 * This function evaluates a SHA3-256 circuit with the provided input,
 * adding proper padding (domain separator 0x06 and end bit 0x80).
 * 
 * @param circuit SHA3-256 circuit to evaluate
 * @param input Input data (up to 136 bytes)
 * @param input_len Input data length
 * @param output Output buffer (must be 32 bytes for SHA3-256)
 * @return true if evaluation was successful, false otherwise
 */
bool evaluate_sha3_circuit(circuit_t *circuit, const uint8_t *input, size_t input_len, uint8_t *output) {
    if (!circuit || !input || !output) {
        return false;
    }
    
    // Validate input length
    if (input_len > 136) {  // SHA3-256 has rate of 136 bytes
        LOG_ERROR("sha3", "Input too large for SHA3-256: %zu bytes (max 136)", input_len);
        return false;
    }
    
    // Convert input to bits (with padding)
    uint8_t *input_bits = safe_calloc(1088, sizeof(uint8_t));
    if (!input_bits) {
        return false;
    }
    
    // Copy input bits (LSB first within each byte)
    size_t bit_pos = 0;
    for (size_t i = 0; i < input_len && bit_pos < 1088; i++) {
        for (int j = 0; j < 8 && bit_pos < 1088; j++) {
            input_bits[bit_pos++] = (input[i] >> j) & 1;
        }
    }
    
    // Add domain separator (0x06 = 0110 in binary) after input
    if (bit_pos < 1088) {
        input_bits[bit_pos++] = 0; // First bit of 0x06 (0110)
        input_bits[bit_pos++] = 1; 
        input_bits[bit_pos++] = 1;
        input_bits[bit_pos++] = 0;
    }
    
    // Add end bit (0x80) at the end of the block
    input_bits[1087] = 1;
    
    // Initialize wire state
    wire_state_t *state = evaluator_init_wire_state(circuit);
    if (!state) {
        free(input_bits);
        return false;
    }
    
    // Set input bits
    if (!evaluator_set_inputs(state, input_bits, 1088)) {
        evaluator_free_wire_state(state);
        free(input_bits);
        return false;
    }
    
    // Evaluate circuit
    if (!evaluator_evaluate_circuit(circuit, state)) {
        evaluator_free_wire_state(state);
        free(input_bits);
        return false;
    }
    
    // Get output bits
    uint8_t output_bits[256];
    if (!evaluator_get_outputs(circuit, state, output_bits)) {
        evaluator_free_wire_state(state);
        free(input_bits);
        return false;
    }
    
    // Convert output bits to bytes
    for (int i = 0; i < 32; i++) {
        output[i] = 0;
        for (int j = 0; j < 8; j++) {
            output[i] |= (output_bits[i * 8 + j] << (7 - j));
        }
    }
    
    evaluator_free_wire_state(state);
    free(input_bits);
    return true;
}