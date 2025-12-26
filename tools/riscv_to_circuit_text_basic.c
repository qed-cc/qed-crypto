/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* Parse RISC-V compiler format and convert to circuit_io text format */
int main(int argc, char *argv[]) {
    if (argc != 3) {
        fprintf(stderr, "Usage: %s <input_file> <output_file>\n", argv[0]);
        fprintf(stderr, "Converts RISC-V compiler circuit format to circuit_io text format\n");
        return 1;
    }

    FILE *in = fopen(argv[1], "r");
    if (!in) {
        fprintf(stderr, "Error: Cannot open input file '%s'\n", argv[1]);
        return 1;
    }

    FILE *out = fopen(argv[2], "w");
    if (!out) {
        fprintf(stderr, "Error: Cannot open output file '%s'\n", argv[2]);
        fclose(in);
        return 1;
    }

    char line[1024];
    uint32_t num_inputs = 0;
    uint32_t num_outputs = 0;
    uint32_t num_gates = 0;
    
    /* First pass: read header info */
    while (fgets(line, sizeof(line), in)) {
        if (strncmp(line, "CIRCUIT_INPUTS", 14) == 0) {
            sscanf(line, "CIRCUIT_INPUTS %u", &num_inputs);
        } else if (strncmp(line, "CIRCUIT_OUTPUTS", 15) == 0) {
            sscanf(line, "CIRCUIT_OUTPUTS %u", &num_outputs);
        } else if (strncmp(line, "CIRCUIT_GATES", 13) == 0) {
            sscanf(line, "CIRCUIT_GATES %u", &num_gates);
            break;
        }
    }

    /* For now, assume 1024 inputs and 32 outputs if not specified (typical RISC-V state) */
    if (num_inputs == 0) {
        num_inputs = 1024; /* 32 registers * 32 bits */
    }
    if (num_outputs == 0) {
        num_outputs = 32; /* Just output one register for testing */
    }

    /* Write circuit_io header */
    fprintf(out, "# Converted from RISC-V compiler format\n");
    fprintf(out, "%u %u %u\n", num_inputs, num_gates, num_outputs);
    fprintf(out, "# Gates follow (type left right output)\n");

    /* Track highest output wire to determine actual outputs */
    uint32_t *output_wires = malloc(num_outputs * sizeof(uint32_t));
    uint32_t highest_output = 0;
    
    /* Second pass: read and convert gates */
    rewind(in);
    
    /* Skip to gates section */
    while (fgets(line, sizeof(line), in)) {
        if (strncmp(line, "CIRCUIT_GATES", 13) == 0) {
            break;
        }
    }

    /* Read and convert gates */
    uint32_t gate_count = 0;
    while (fgets(line, sizeof(line), in) && gate_count < num_gates) {
        /* Skip comments and empty lines */
        if (line[0] == '#' || line[0] == '\n') {
            continue;
        }

        uint32_t gate_id, left, right, output;
        char gate_type_str[10];
        
        if (sscanf(line, "%u %u %u %u %s", &gate_id, &left, &right, &output, gate_type_str) == 5) {
            /* Convert gate type from string to number */
            uint32_t gate_type = (strcmp(gate_type_str, "AND") == 0) ? 0 : 1;
            
            /* Write in circuit_io format: type left right output */
            fprintf(out, "%u %u %u %u\n", gate_type, left, right, output);
            
            if (output > highest_output) {
                highest_output = output;
            }
            
            gate_count++;
        }
    }

    fprintf(out, "\n");
    fprintf(out, "# Output wires\n");

    /* For output wires, just use the last N wires as outputs */
    /* This is a simplification - in reality we'd need to know which wires map to output registers */
    for (uint32_t i = 0; i < num_outputs; i++) {
        uint32_t output_wire = highest_output - num_outputs + i + 1;
        fprintf(out, "%u\n", output_wire);
    }

    free(output_wires);
    fclose(in);
    fclose(out);

    printf("Conversion complete:\n");
    printf("  Input gates: %u\n", num_gates);
    printf("  Input bits: %u\n", num_inputs);
    printf("  Output bits: %u\n", num_outputs);
    printf("  Highest wire: %u\n", highest_output);

    return 0;
}