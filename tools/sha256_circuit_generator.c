/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * sha256_circuit_generator.c - Direct SHA-256 circuit generator
 * 
 * Generates a real SHA-256 circuit with ~340K gates for Bitcoin verification
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "input_validation.h"

// SHA-256 constants
static const uint32_t K[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

// Initial hash values  
static const uint32_t H0[8] = {
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
};

typedef struct {
    uint32_t num_inputs;
    uint32_t num_outputs; 
    uint32_t num_gates;
    uint32_t next_wire_id;
    FILE* output_file;
} circuit_builder_t;

// Circuit building helpers
static uint32_t allocate_wire(circuit_builder_t* builder) {
    return builder->next_wire_id++;
}

// Allocate 32 wires for a 32-bit word
static void allocate_word_wires(circuit_builder_t* builder, uint32_t wires[32]) {
    for (int i = 0; i < 32; i++) {
        wires[i] = allocate_wire(builder);
    }
}

// Add a gate: out = left op right (where op is 0=AND, 1=XOR)
static void add_gate(circuit_builder_t* builder, uint32_t left, uint32_t right, uint32_t out, int gate_type) {
    fprintf(builder->output_file, "%d %u %u %u\n", gate_type, left, right, out);
    builder->num_gates++;
}

// XOR two 32-bit words: out = a XOR b (32 gates)
static void add_word_xor(circuit_builder_t* builder, uint32_t a[32], uint32_t b[32], uint32_t out[32]) {
    for (int i = 0; i < 32; i++) {
        add_gate(builder, a[i], b[i], out[i], 1); // XOR
    }
}

// AND two 32-bit words: out = a AND b (32 gates)  
static void add_word_and(circuit_builder_t* builder, uint32_t a[32], uint32_t b[32], uint32_t out[32]) {
    for (int i = 0; i < 32; i++) {
        add_gate(builder, a[i], b[i], out[i], 0); // AND
    }
}

// NOT a 32-bit word: out = NOT a (32 gates - XOR with 1)
static void add_word_not(circuit_builder_t* builder, uint32_t a[32], uint32_t out[32]) {
    for (int i = 0; i < 32; i++) {
        add_gate(builder, a[i], 2, out[i], 1); // XOR with constant 1 (wire 2)
    }
}

// Ripple-carry adder: out = a + b (224 gates for 32-bit)
static void add_word_add(circuit_builder_t* builder, uint32_t a[32], uint32_t b[32], uint32_t out[32]) {
    uint32_t carry = 1; // Start with constant 0 (wire 1)
    
    for (int i = 0; i < 32; i++) {
        uint32_t sum_temp = allocate_wire(builder);
        uint32_t carry_temp1 = allocate_wire(builder);
        uint32_t carry_temp2 = allocate_wire(builder);
        uint32_t new_carry = allocate_wire(builder);
        
        // sum = a[i] XOR b[i] XOR carry
        add_gate(builder, a[i], b[i], sum_temp, 1); // XOR
        add_gate(builder, sum_temp, carry, out[i], 1); // XOR
        
        // carry_out = (a[i] AND b[i]) OR (sum_temp AND carry)
        add_gate(builder, a[i], b[i], carry_temp1, 0); // AND
        add_gate(builder, sum_temp, carry, carry_temp2, 0); // AND  
        add_gate(builder, carry_temp1, carry_temp2, new_carry, 1); // XOR (OR in GF(2))
        
        carry = new_carry;
    }
}

// Rotate right: out = rotr(a, n) - uses barrel shifter approach
static void add_word_rotr(circuit_builder_t* builder, uint32_t a[32], int n, uint32_t out[32]) {
    // For constant rotation, just rewire
    for (int i = 0; i < 32; i++) {
        int src_bit = (i + n) % 32;
        add_gate(builder, a[src_bit], 1, out[i], 1); // XOR with 0 (identity)
    }
}

// Right shift: out = a >> n
static void add_word_shr(circuit_builder_t* builder, uint32_t a[32], int n, uint32_t out[32]) {
    for (int i = 0; i < 32; i++) {
        if (i + n < 32) {
            add_gate(builder, a[i + n], 1, out[i], 1); // XOR with 0 (identity)
        } else {
            add_gate(builder, 1, 1, out[i], 1); // XOR with 0 = 0
        }
    }
}

// CH function: out = (x & y) ^ (~x & z) - 96 gates
static void add_ch(circuit_builder_t* builder, uint32_t x[32], uint32_t y[32], uint32_t z[32], uint32_t out[32]) {
    uint32_t not_x[32], xy[32], not_x_z[32];
    
    allocate_word_wires(builder, not_x);
    allocate_word_wires(builder, xy);
    allocate_word_wires(builder, not_x_z);
    
    add_word_not(builder, x, not_x);           // 32 gates
    add_word_and(builder, x, y, xy);           // 32 gates
    add_word_and(builder, not_x, z, not_x_z); // 32 gates
    add_word_xor(builder, xy, not_x_z, out);   // 32 gates = 96 total
}

// MAJ function: out = (x & y) ^ (x & z) ^ (y & z) - 96 gates
static void add_maj(circuit_builder_t* builder, uint32_t x[32], uint32_t y[32], uint32_t z[32], uint32_t out[32]) {
    uint32_t xy[32], xz[32], yz[32], temp[32];
    
    allocate_word_wires(builder, xy);
    allocate_word_wires(builder, xz);
    allocate_word_wires(builder, yz);
    allocate_word_wires(builder, temp);
    
    add_word_and(builder, x, y, xy);        // 32 gates
    add_word_and(builder, x, z, xz);        // 32 gates
    add_word_and(builder, y, z, yz);        // 32 gates
    add_word_xor(builder, xy, xz, temp);    // 32 gates
    add_word_xor(builder, temp, yz, out);   // 32 gates = 160 total
}

// SIGMA0: out = rotr(x,2) ^ rotr(x,13) ^ rotr(x,22) - 64 gates (rotations are free)
static void add_sigma0(circuit_builder_t* builder, uint32_t x[32], uint32_t out[32]) {
    uint32_t rot2[32], rot13[32], rot22[32], temp[32];
    
    allocate_word_wires(builder, rot2);
    allocate_word_wires(builder, rot13);
    allocate_word_wires(builder, rot22);
    allocate_word_wires(builder, temp);
    
    add_word_rotr(builder, x, 2, rot2);
    add_word_rotr(builder, x, 13, rot13);
    add_word_rotr(builder, x, 22, rot22);
    add_word_xor(builder, rot2, rot13, temp);
    add_word_xor(builder, temp, rot22, out);
}

// SIGMA1: out = rotr(x,6) ^ rotr(x,11) ^ rotr(x,25) - 64 gates
static void add_sigma1(circuit_builder_t* builder, uint32_t x[32], uint32_t out[32]) {
    uint32_t rot6[32], rot11[32], rot25[32], temp[32];
    
    allocate_word_wires(builder, rot6);
    allocate_word_wires(builder, rot11);
    allocate_word_wires(builder, rot25);
    allocate_word_wires(builder, temp);
    
    add_word_rotr(builder, x, 6, rot6);
    add_word_rotr(builder, x, 11, rot11);
    add_word_rotr(builder, x, 25, rot25);
    add_word_xor(builder, rot6, rot11, temp);
    add_word_xor(builder, temp, rot25, out);
}

// Load constant into wire array
static void load_constant(circuit_builder_t* builder, uint32_t value, uint32_t out[32]) {
    for (int i = 0; i < 32; i++) {
        if (value & (1U << i)) {
            add_gate(builder, 2, 1, out[i], 1); // XOR 1 with 0 = 1
        } else {
            add_gate(builder, 1, 1, out[i], 1); // XOR 0 with 0 = 0
        }
    }
}

// Generate SHA-256 compression function circuit
static void generate_sha256_compression(circuit_builder_t* builder, 
                                       uint32_t state_in[8][32],
                                       uint32_t block[16][32],
                                       uint32_t state_out[8][32]) {
    
    uint32_t W[64][32];
    uint32_t a[32], b[32], c[32], d[32], e[32], f[32], g[32], h[32];
    
    // Initialize working variables from input state
    for (int i = 0; i < 32; i++) {
        a[i] = state_in[0][i];
        b[i] = state_in[1][i];
        c[i] = state_in[2][i];
        d[i] = state_in[3][i];
        e[i] = state_in[4][i];
        f[i] = state_in[5][i];
        g[i] = state_in[6][i];
        h[i] = state_in[7][i];
    }
    
    // Copy first 16 words from block
    for (int i = 0; i < 16; i++) {
        for (int j = 0; j < 32; j++) {
            W[i][j] = block[i][j];
        }
    }
    
    // Extend to 64 words (message schedule)
    for (int i = 16; i < 64; i++) {
        uint32_t temp_wires[5][32];
        for (int j = 0; j < 5; j++) {
            allocate_word_wires(builder, temp_wires[j]);
        }
        
        // gamma1(W[i-2])
        add_word_rotr(builder, W[i-2], 17, temp_wires[0]);
        add_word_rotr(builder, W[i-2], 19, temp_wires[1]);
        add_word_shr(builder, W[i-2], 10, temp_wires[2]);
        add_word_xor(builder, temp_wires[0], temp_wires[1], temp_wires[3]);
        add_word_xor(builder, temp_wires[3], temp_wires[2], temp_wires[4]); // gamma1 result
        
        // W[i] = gamma1(W[i-2]) + W[i-7] + gamma0(W[i-15]) + W[i-16]
        uint32_t sum_temp[4][32];
        for (int j = 0; j < 4; j++) {
            allocate_word_wires(builder, sum_temp[j]);
        }
        
        // gamma0(W[i-15]) 
        uint32_t gamma0_temp[4][32];
        for (int j = 0; j < 4; j++) {
            allocate_word_wires(builder, gamma0_temp[j]);
        }
        add_word_rotr(builder, W[i-15], 7, gamma0_temp[0]);
        add_word_rotr(builder, W[i-15], 18, gamma0_temp[1]);
        add_word_shr(builder, W[i-15], 3, gamma0_temp[2]);
        add_word_xor(builder, gamma0_temp[0], gamma0_temp[1], gamma0_temp[3]);
        add_word_xor(builder, gamma0_temp[3], gamma0_temp[2], sum_temp[0]); // gamma0 result
        
        add_word_add(builder, temp_wires[4], W[i-7], sum_temp[1]);      // gamma1 + W[i-7]
        add_word_add(builder, sum_temp[1], sum_temp[0], sum_temp[2]);    // + gamma0
        add_word_add(builder, sum_temp[2], W[i-16], W[i]);              // + W[i-16]
        
        allocate_word_wires(builder, W[i]);
        for (int j = 0; j < 32; j++) {
            W[i][j] = sum_temp[2][j];
        }
    }
    
    // Main compression loop (64 rounds)
    for (int i = 0; i < 64; i++) {
        uint32_t temp_wires[10][32];
        for (int j = 0; j < 10; j++) {
            allocate_word_wires(builder, temp_wires[j]);
        }
        
        uint32_t K_wire[32];
        allocate_word_wires(builder, K_wire);
        load_constant(builder, K[i], K_wire);
        
        // T1 = h + SIGMA1(e) + CH(e,f,g) + K[i] + W[i]
        add_sigma1(builder, e, temp_wires[0]);                          // SIGMA1(e)
        add_ch(builder, e, f, g, temp_wires[1]);                        // CH(e,f,g)
        add_word_add(builder, h, temp_wires[0], temp_wires[2]);         // h + SIGMA1
        add_word_add(builder, temp_wires[2], temp_wires[1], temp_wires[3]); // + CH
        add_word_add(builder, temp_wires[3], K_wire, temp_wires[4]);    // + K[i]
        add_word_add(builder, temp_wires[4], W[i], temp_wires[5]);      // + W[i] = T1
        
        // T2 = SIGMA0(a) + MAJ(a,b,c)
        add_sigma0(builder, a, temp_wires[6]);                          // SIGMA0(a)
        add_maj(builder, a, b, c, temp_wires[7]);                       // MAJ(a,b,c)
        add_word_add(builder, temp_wires[6], temp_wires[7], temp_wires[8]); // T2
        
        // Update working variables
        uint32_t new_a[32], new_e[32];
        allocate_word_wires(builder, new_a);
        allocate_word_wires(builder, new_e);
        
        add_word_add(builder, temp_wires[5], temp_wires[8], new_a);     // T1 + T2
        add_word_add(builder, d, temp_wires[5], new_e);                 // d + T1
        
        // Shift registers: h=g, g=f, f=e, e=new_e, d=c, c=b, b=a, a=new_a
        for (int j = 0; j < 32; j++) {
            h[j] = g[j];
            g[j] = f[j];
            f[j] = e[j];
            e[j] = new_e[j];
            d[j] = c[j];
            c[j] = b[j];
            b[j] = a[j];
            a[j] = new_a[j];
        }
    }
    
    // Add to output state
    add_word_add(builder, state_in[0], a, state_out[0]);
    add_word_add(builder, state_in[1], b, state_out[1]);
    add_word_add(builder, state_in[2], c, state_out[2]);
    add_word_add(builder, state_in[3], d, state_out[3]);
    add_word_add(builder, state_in[4], e, state_out[4]);
    add_word_add(builder, state_in[5], f, state_out[5]);
    add_word_add(builder, state_in[6], g, state_out[6]);
    add_word_add(builder, state_in[7], h, state_out[7]);
}

// Generate complete SHA-256 circuit for single block
void generate_sha256_circuit(const char* output_filename) {
    // Use string buffer to collect gates, then write at end
    circuit_builder_t builder = {0};
    builder.output_file = NULL; // Will write to buffer first
    builder.next_wire_id = 3; // Start after constants 0,1,2
    
    // Create temporary file for gates
    FILE* temp_file = tmpfile();
    if (!temp_file) {
        fprintf(stderr, "Error: Cannot create temporary file\n");
        return;
    }
    builder.output_file = temp_file;
    
    // Allocate input wires (512 bits = 16 words)
    uint32_t input_block[16][32];
    for (int i = 0; i < 16; i++) {
        allocate_word_wires(&builder, input_block[i]);
    }
    builder.num_inputs = 16 * 32; // 512 input bits
    
    // Allocate initial state wires (can be constants for SHA-256)
    uint32_t initial_state[8][32];
    for (int i = 0; i < 8; i++) {
        allocate_word_wires(&builder, initial_state[i]);
        load_constant(&builder, H0[i], initial_state[i]);
    }
    
    // Allocate output state wires
    uint32_t output_state[8][32];
    for (int i = 0; i < 8; i++) {
        allocate_word_wires(&builder, output_state[i]);
    }
    builder.num_outputs = 8 * 32; // 256 output bits
    
    // Generate the compression function circuit
    generate_sha256_compression(&builder, initial_state, input_block, output_state);
    
    // Now write the final circuit file
    FILE* f = fopen(output_filename, "w");
    if (!f) {
        fprintf(stderr, "Error: Cannot open output file %s\n", output_filename);
        fclose(temp_file);
        return;
    }
    
    // Write header
    fprintf(f, "%u %u %u\n", builder.num_inputs, builder.num_gates, builder.num_outputs);
    
    // Copy gates from temp file
    rewind(temp_file);
    char buffer[1024];
    while (fgets(buffer, sizeof(buffer), temp_file)) {
        fputs(buffer, f);
    }
    fclose(temp_file);
    
    // Write output wire list
    for (int i = 0; i < 8; i++) {
        for (int j = 0; j < 32; j++) {
            fprintf(f, "%u\n", output_state[i][j]);
        }
    }
    
    fclose(f);
    
    printf("✅ SHA-256 circuit generated: %s\n", output_filename);
    printf("   Circuit statistics:\n");
    printf("   - Input bits: %u (512-bit block)\n", builder.num_inputs);
    printf("   - Output bits: %u (256-bit hash)\n", builder.num_outputs);
    printf("   - Total gates: %u\n", builder.num_gates);
    printf("   - Total wires: %u\n", builder.next_wire_id);
    printf("   - Estimated for Bitcoin: 2 * %u = %u gates (double SHA-256)\n", 
           builder.num_gates, builder.num_gates * 2);
}

int main(int argc, char* argv[]) {
    if (argc != 2) {
        printf("Usage: %s <output_circuit_file>\n", argv[0]);
        printf("Generates a SHA-256 circuit in gate_computer text format\n");
        return 1;
    }
    
    // Validate output file path
    if (validate_file_path(argv[1], true, MAX_PATH_LENGTH) != VALIDATION_SUCCESS) {
        printf("Error: Invalid output file path: %s\n", argv[1]);
        return 1;
    }
    
    generate_sha256_circuit(argv[1]);
    return 0;
}