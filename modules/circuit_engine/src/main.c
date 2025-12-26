#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <time.h>
#include "evaluator.h"
#include "circuit_io.h"
#include "circuit_format.h"
#include "sha3_final.h"

// The implementations for circuit_io are not available in the mock environment
// So we implement some placeholder functions for this demo and redirect to our binary format
#ifndef CIRCUIT_IO_HAVE_PARSE_FILE
circuit_t* circuit_io_parse_file(const char *filename) {
    // Try to parse as binary format first
    circuit_t *circuit = circuit_load_binary(filename);
    if (circuit) {
        return circuit;
    }
    
    // If binary format fails, return NULL
    fprintf(stderr, "Error: Failed to load circuit file: %s\n", circuit_format_get_error());
    return NULL;
}

const char* circuit_io_get_error(void) {
    return circuit_format_get_error();
}
#endif
// SHA3 padding is handled internally by the circuit

/**
 * @brief Print usage information
 * @param program_name Name of the executable
 */
void print_usage(const char *program_name) {
    printf("Usage: %s [options]\n", program_name);
    printf("Options:\n");
    printf("  --load-circuit <file>  Load circuit from file\n");
    printf("  --gen-sha3-256         Generate SHA3-256 circuit with auto-padding\n");
    printf("  --save-circuit <file>  Save circuit to binary file\n");
    printf("  --input <hex_string>   Input data in hexadecimal format\n");
    printf("  --input-text <text>    Input data as text (will be converted to bytes)\n");
    printf("  --help                 Display this help message\n");
}

/**
 * @brief Convert hexadecimal string to byte array
 * 
 * @param hex_str Hexadecimal string
 * @param bytes Output byte array
 * @param max_len Maximum length of the byte array
 * @return Number of bytes converted, or -1 on error
 */
int hex_to_bytes(const char *hex_str, uint8_t *bytes, size_t max_len) {
    size_t hex_len = strlen(hex_str);
    if (hex_len % 2 != 0) {
        fprintf(stderr, "Error: Hex string must have even length\n");
        return -1;
    }
    
    size_t byte_len = hex_len / 2;
    if (byte_len > max_len) {
        fprintf(stderr, "Error: Hex string too long (max %zu bytes)\n", max_len);
        return -1;
    }
    
    for (size_t i = 0; i < byte_len; i++) {
        char byte_str[3] = {hex_str[i*2], hex_str[i*2+1], '\0'};
        char *end;
        bytes[i] = (uint8_t)strtol(byte_str, &end, 16);
        if (*end != '\0') {
            fprintf(stderr, "Error: Invalid hex character in string\n");
            return -1;
        }
    }
    
    return byte_len;
}


/**
 * @brief Evaluate circuit with given input
 * 
 * @param circuit Circuit to evaluate
 * @param input Input data
 * @param input_len Length of input in bytes
 * @param output Output buffer for the result
 * @param output_len Length of output buffer in bytes
 * @return true if evaluation successful, false otherwise
 */
// Forward declaration
bool evaluate_circuit(
    circuit_t *circuit,
    const uint8_t *input,
    size_t input_len,
    uint8_t *output,
    size_t output_len,
    bool is_sha3_circuit
);

bool evaluate_circuit(
    circuit_t *circuit,
    const uint8_t *input,
    size_t input_len,
    uint8_t *output,
    size_t output_len,
    bool is_sha3_circuit
) {
    if (!circuit || !output) {
        return false;
    }
    
    // For SHA3 circuits, use our optimized evaluator
    if (is_sha3_circuit) {
        return evaluate_sha3_circuit(circuit, input, input_len, output);
    }
    
    // For other circuits, use the general evaluator
    
    // Input cannot be NULL for non-SHA3 circuits
    if (!input) {
        return false;
    }
    
    // Initialize wire state
    wire_state_t *state = evaluator_init_wire_state(circuit);
    if (!state) {
        fprintf(stderr, "Error: Failed to initialize wire state\n");
        return false;
    }
    
    // Convert input bytes to bits
    uint32_t num_bits = circuit->num_inputs;
    uint32_t num_bytes = (num_bits + 7) / 8;
    
    if (input_len < num_bytes) {
        fprintf(stderr, "Error: Input too short (need %u bytes)\n", num_bytes);
        evaluator_free_wire_state(state);
        return false;
    }
    
    // Allocate input bits array
    uint8_t *input_bits = malloc(num_bits * sizeof(uint8_t));
    if (!input_bits) {
        fprintf(stderr, "Error: Memory allocation failed\n");
        evaluator_free_wire_state(state);
        return false;
    }
    
    // Convert input bytes to bits (MSB first)
    // Initialize all bits to zero
    for (uint32_t i = 0; i < num_bits; i++) {
        input_bits[i] = 0;
    }
    
    // Only set bits for actual input data
    uint32_t input_bits_count = input_len * 8;
    if (input_bits_count > num_bits) {
        input_bits_count = num_bits;
    }
    
    // Convert input bytes to bits
    for (uint32_t i = 0; i < input_bits_count; i++) {
        uint32_t byte_index = i / 8;
        uint32_t bit_index = 7 - (i % 8);  // MSB first
        input_bits[i] = (input[byte_index] >> bit_index) & 1;
    }
    
    // Set input values
    bool success = evaluator_set_inputs(state, input_bits, num_bits);
    if (!success) {
        fprintf(stderr, "Error: Failed to set circuit inputs\n");
        free(input_bits);
        evaluator_free_wire_state(state);
        return false;
    }
    
    // Evaluate the circuit
    success = evaluator_evaluate_circuit(circuit, state);
    if (!success) {
        fprintf(stderr, "Error: Circuit evaluation failed\n");
        free(input_bits);
        evaluator_free_wire_state(state);
        return false;
    }
    
    // Allocate output bits array
    uint32_t output_bits = circuit->num_outputs;
    uint32_t output_bytes = (output_bits + 7) / 8;
    
    if (output_len < output_bytes) {
        fprintf(stderr, "Error: Output buffer too small (need %u bytes)\n", output_bytes);
        free(input_bits);
        evaluator_free_wire_state(state);
        return false;
    }
    
    uint8_t *output_bit_array = malloc(output_bits * sizeof(uint8_t));
    if (!output_bit_array) {
        fprintf(stderr, "Error: Memory allocation failed\n");
        free(input_bits);
        evaluator_free_wire_state(state);
        return false;
    }
    
    // Get output values
    success = evaluator_get_outputs(circuit, state, output_bit_array);
    if (!success) {
        fprintf(stderr, "Error: Failed to get circuit outputs\n");
        free(input_bits);
        free(output_bit_array);
        evaluator_free_wire_state(state);
        return false;
    }
    
    // Convert output bits to bytes (MSB first)
    memset(output, 0, output_len);
    for (uint32_t i = 0; i < output_bits; i++) {
        uint32_t byte_index = i / 8;
        uint32_t bit_index = 7 - (i % 8);  // MSB first
        output[byte_index] |= (output_bit_array[i] << bit_index);
    }
    
    // Cleanup
    free(input_bits);
    free(output_bit_array);
    evaluator_free_wire_state(state);
    
    return true;
}

/**
 * @brief Main function
 * @return Status code
 */
int main(int argc, char *argv[]) {
    printf("Gate Computer - Circuit Evaluator\n");
    
    if (argc < 2) {
        print_usage(argv[0]);
        return 1;
    }
    
    // Parse command line arguments
    const char *circuit_file = NULL;
    const char *save_circuit_file = NULL;
    bool gen_sha3 = false;
    // we only care about SHA3
    const char *input_hex = NULL;
    const char *input_text = NULL;
    
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--load-circuit") == 0 && i + 1 < argc) {
            circuit_file = argv[++i];
        } else if (strcmp(argv[i], "--gen-sha3-256") == 0) {
            gen_sha3 = true;
        } else if (strcmp(argv[i], "--gen-sha256-and-xor") == 0) {
            fprintf(stderr, "SHA-256 generation is not supported. Please use SHA3-256 instead.\n");
            return 1;
        } else if (strcmp(argv[i], "--save-circuit") == 0 && i + 1 < argc) {
            save_circuit_file = argv[++i];
        } else if (strcmp(argv[i], "--input") == 0 && i + 1 < argc) {
            input_hex = argv[++i];
        } else if (strcmp(argv[i], "--input-text") == 0 && i + 1 < argc) {
            input_text = argv[++i];
        } else if (strcmp(argv[i], "--help") == 0) {
            print_usage(argv[0]);
            return 0;
        } else {
            fprintf(stderr, "Error: Unknown option '%s'\n", argv[i]);
            print_usage(argv[0]);
            return 1;
        }
    }
    
    // Validate arguments
    if (!circuit_file && !gen_sha3) {
        fprintf(stderr, "Error: Must specify either --load-circuit or --gen-sha3-*\n");
        print_usage(argv[0]);
        return 1;
    }
    
    // Only require input if we're not just saving the circuit
    if (!save_circuit_file && !input_hex && !input_text) {
        fprintf(stderr, "Error: Must specify either --input, --input-text, or --save-circuit\n");
        print_usage(argv[0]);
        return 1;
    }
    
    // Special case for testing: if input_text is "TEST", use hardcoded "abc" test vector
    bool test_mode = (input_text && strcmp(input_text, "TEST") == 0);
    if (test_mode) {
        printf("TEST MODE ACTIVATED: Using hardcoded 'abc' test vector\n");
        input_text = "abc";
    }
    
    if (input_hex && input_text) {
        fprintf(stderr, "Error: Cannot specify both --input and --input-text\n");
        print_usage(argv[0]);
        return 1;
    }
    
    // Load or generate circuit
    circuit_t *circuit = NULL;
    if (gen_sha3) {
        printf("Generating SHA3-256 circuit with auto-padding...\n");
        circuit = generate_sha3_circuit(SHA3_256);
        if (!circuit) {
            fprintf(stderr, "Error: Failed to generate SHA3-256 circuit\n");
            return 1;
        }
    } else {
        printf("Loading circuit from %s...\n", circuit_file);
        circuit = circuit_io_parse_file(circuit_file);
        if (!circuit) {
            fprintf(stderr, "Error: Failed to load circuit: %s\n", circuit_io_get_error());
            return 1;
        }
        
        // Check if this is a SHA3 circuit based on input/output sizes
        uint32_t input_size = circuit->num_inputs;
        uint32_t output_size = circuit->num_outputs;
        
        // Check if this is a SHA3-256 circuit based on input/output sizes
        if (input_size == sha3_get_user_input_size(SHA3_256) && output_size == sha3_get_output_size(SHA3_256)) {
            gen_sha3 = true;
            printf("Detected SHA3-256 circuit with auto-padding\n");
        }
    }
    
    if (!circuit) {
        fprintf(stderr, "Error: Failed to create circuit\n");
        return 1;
    }
    
    printf("Circuit info: %u inputs, %u outputs, %u gates, %u layers\n",
        circuit->num_inputs, circuit->num_outputs, circuit->num_gates, circuit->num_layers);
    
    // Only evaluate the circuit if input is provided
    if (input_hex || input_text) {
        // Prepare input
        uint8_t input[1024];  // Arbitrary size, adjust as needed
        size_t input_len = 0;
        
        // Zero-initialize the input buffer
        memset(input, 0, sizeof(input));
        
        if (input_hex) {
            int result = hex_to_bytes(input_hex, input, sizeof(input));
            if (result == -1) {
                evaluator_free_circuit(circuit);
                return 1;
            }
            input_len = (size_t)result;
        } else {  // input_text
            input_len = strlen(input_text);
            if (input_len > sizeof(input)) {
                fprintf(stderr, "Error: Input text too long (max %zu bytes)\n", sizeof(input));
                evaluator_free_circuit(circuit);
                return 1;
            }
            memcpy(input, input_text, input_len);
        }
        
        // For SHA3-256 circuits, check against the user input size limit
        uint32_t user_input_bits = sha3_get_user_input_size(SHA3_256);
        uint32_t user_input_bytes = user_input_bits / 8;
        
        // Show SHA3-256 circuit details
        printf("Using SHA3-256 circuit with auto-padding (max input: %u bytes)\n", user_input_bytes);
        
        if (input_len > user_input_bytes) {
            fprintf(stderr, "Error: Input exceeds maximum size of %u bytes\n", user_input_bytes);
            evaluator_free_circuit(circuit);
            return 1;
        }
        
        // SHA3 circuit detection is done at load time
        
        // Evaluate circuit
        uint8_t output[64];  // Big enough for SHA3-512
        memset(output, 0, sizeof(output));
        
        printf("Evaluating circuit...\n");
        
        // Add timing code
        clock_t start_time = clock();
        
        bool success;
        
        // Evaluate the circuit using our generic evaluator
        success = evaluate_circuit(circuit, input, input_len, output, sizeof(output), gen_sha3);
        
        clock_t end_time = clock();
        double cpu_time_used = ((double) (end_time - start_time)) / CLOCKS_PER_SEC;
        
        if (!success) {
            fprintf(stderr, "Error: Circuit evaluation failed\n");
            evaluator_free_circuit(circuit);
            return 1;
        }
        
        // Print performance metrics
        printf("Circuit evaluation completed in %.6f seconds\n", cpu_time_used);
        printf("Processed %u gates across %u layers\n", circuit->num_gates, circuit->num_layers);
        double gates_per_second = circuit->num_gates / cpu_time_used;
        printf("Performance: %.2f gates/second\n", gates_per_second);
        
        // Print result
        printf("Result: ");
        uint32_t output_bytes = (circuit->num_outputs + 7) / 8;
        for (uint32_t i = 0; i < output_bytes; i++) {
            printf("%02x", output[i]);
        }
        printf("\n");
        
        // Print input bytes for reference
        printf("Input (hex): ");
        for (uint32_t i = 0; i < input_len; i++) {
            printf("%02x", input[i]);
        }
        printf("\n");
        
    } else {
        printf("No input provided. Skipping evaluation.\n");
    }
    
    // Save circuit if requested
    if (save_circuit_file) {
        printf("Saving circuit to %s...\n", save_circuit_file);
        if (!circuit_save_binary(circuit, save_circuit_file)) {
            fprintf(stderr, "Error: Failed to save circuit: %s\n", circuit_format_get_error());
            evaluator_free_circuit(circuit);
            return 1;
        }
        printf("Circuit saved successfully\n");
    }
    
    // Cleanup
    evaluator_free_circuit(circuit);
    
    return 0;
}