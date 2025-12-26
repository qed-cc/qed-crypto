/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * Simple tool to convert text circuit format to binary format
 * This helps create test circuits for development
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "input_validation.h"

#define CIRCUIT_BINARY_MAGIC 0x47434342  // "GCCB"
#define CIRCUIT_BINARY_VERSION 1

typedef struct {
    uint32_t magic;
    uint32_t version;
    uint32_t header_size;
    uint32_t num_inputs;
    uint32_t num_gates;
    uint32_t num_outputs;
    uint32_t num_layers;
    uint32_t gates_offset;
    uint32_t outputs_offset;
    uint32_t layers_offset;
    uint32_t circuit_size;
    uint32_t reserved[5];
} circuit_header_t;

typedef struct {
    uint8_t type;
    uint8_t reserved[3];
    uint32_t input1;
    uint32_t input2;
    uint32_t output;
} gate_t;

int main(int argc, char **argv) {
    if (argc != 3) {
        fprintf(stderr, "Usage: %s input.txt output.bin\n", argv[0]);
        return 1;
    }
    
    // Validate input and output file paths
    if (validate_file_path(argv[1], true, MAX_PATH_LENGTH) != VALIDATION_SUCCESS) {
        fprintf(stderr, "Error: Invalid input file path: %s\n", argv[1]);
        return 1;
    }
    
    if (validate_file_path(argv[2], true, MAX_PATH_LENGTH) != VALIDATION_SUCCESS) {
        fprintf(stderr, "Error: Invalid output file path: %s\n", argv[2]);
        return 1;
    }
    
    FILE *in = fopen(argv[1], "r");
    if (!in) {
        perror("Cannot open input file");
        return 1;
    }
    
    // Parse the text file
    char line[256];
    uint32_t num_inputs = 0, num_outputs = 0, num_gates = 0;
    gate_t *gates = NULL;
    uint32_t gate_count = 0;
    uint32_t max_wire = 0;
    
    while (fgets(line, sizeof(line), in)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        
        if (strncmp(line, "INPUTS", 6) == 0) {
            sscanf(line, "INPUTS %u", &num_inputs);
        } else if (strncmp(line, "OUTPUTS", 7) == 0) {
            sscanf(line, "OUTPUTS %u", &num_outputs);
        } else if (strncmp(line, "GATES", 5) == 0) {
            sscanf(line, "GATES %u", &num_gates);
            gates = calloc(num_gates, sizeof(gate_t));
            if (!gates) {
                fprintf(stderr, "Failed to allocate memory for gates\n");
                fclose(in);
                return 1;
            }
        } else if (strncmp(line, "GATE", 4) == 0) {
            char type[10];
            uint32_t in1, in2, out;
            sscanf(line, "GATE %s %u %u %u", type, &in1, &in2, &out);
            
            if (gate_count < num_gates) {
                gates[gate_count].type = (strcmp(type, "AND") == 0) ? 0 : 1;
                gates[gate_count].input1 = in1;
                gates[gate_count].input2 = in2;
                gates[gate_count].output = out;
                
                if (out > max_wire) max_wire = out;
                gate_count++;
            }
        }
    }
    fclose(in);
    
    // Determine output wires (last num_outputs wires)
    uint32_t *output_wires = calloc(num_outputs, sizeof(uint32_t));
    if (!output_wires) {
        fprintf(stderr, "Failed to allocate memory for output wires\n");
        free(gates);
        return 1;
    }
    for (uint32_t i = 0; i < num_outputs; i++) {
        output_wires[i] = max_wire - num_outputs + i + 1;
    }
    
    // Write binary file
    FILE *out = fopen(argv[2], "wb");
    if (!out) {
        perror("Cannot create output file");
        free(gates);
        free(output_wires);
        return 1;
    }
    
    // Prepare header
    circuit_header_t header = {0};
    header.magic = CIRCUIT_BINARY_MAGIC;
    header.version = CIRCUIT_BINARY_VERSION;
    header.header_size = sizeof(header);
    header.num_inputs = num_inputs;
    header.num_gates = num_gates;
    header.num_outputs = num_outputs;
    header.num_layers = 1;  // Simple circuits, all gates in one layer
    header.gates_offset = sizeof(header);
    header.outputs_offset = sizeof(header) + num_gates * sizeof(gate_t);
    header.layers_offset = header.outputs_offset + num_outputs * sizeof(uint32_t);
    
    // Write header
    fwrite(&header, sizeof(header), 1, out);
    
    // Write gates
    fwrite(gates, sizeof(gate_t), num_gates, out);
    
    // Write output wires
    fwrite(output_wires, sizeof(uint32_t), num_outputs, out);
    
    // Write layer offset (just one layer starting at gate 0)
    uint32_t layer_offset = 0;
    fwrite(&layer_offset, sizeof(uint32_t), 1, out);
    
    fclose(out);
    free(gates);
    free(output_wires);
    
    printf("Converted %s to %s\n", argv[1], argv[2]);
    printf("Circuit: %u inputs, %u outputs, %u gates\n", 
           num_inputs, num_outputs, num_gates);
    
    return 0;
}