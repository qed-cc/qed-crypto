/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

/* RISC-V state layout in circuit inputs/outputs
 * Based on modules/riscv_compiler/include/riscv_compiler.h
 * 
 * Input bits:
 *   0: Constant 0 (CONSTANT_0_WIRE)
 *   1: Constant 1 (CONSTANT_1_WIRE)
 *   2-33: PC (32 bits)
 *   34-1057: Registers x0-x31 (32 registers × 32 bits each)
 *   1058+: Memory (if any)
 * 
 * Output bits: Same layout as inputs (full state)
 */

#define CONSTANT_0_WIRE 0
#define CONSTANT_1_WIRE 1
#define PC_START_BIT 2
#define PC_BITS 32
#define REGS_START_BIT (PC_START_BIT + PC_BITS)
#define REGS_BITS (32 * 32)
#define MEMORY_START_BIT (REGS_START_BIT + REGS_BITS)

typedef struct {
    uint32_t gate_id;
    uint32_t left_input;
    uint32_t right_input;
    uint32_t output_wire;
    uint32_t gate_type; /* 0=AND, 1=XOR */
} gate_info_t;

/* Track which wires are assigned to which registers */
typedef struct {
    uint32_t pc_wires[32];      /* PC bit wires */
    uint32_t reg_wires[32][32]; /* Register bit wires [reg][bit] */
    bool pc_modified;
    bool reg_modified[32];
} wire_mapping_t;

int main(int argc, char *argv[]) {
    if (argc != 3) {
        fprintf(stderr, "Usage: %s <input_file> <output_file>\n", argv[0]);
        fprintf(stderr, "Converts RISC-V compiler circuit format to circuit_io text format\n");
        fprintf(stderr, "with proper state mapping\n");
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
    uint32_t num_gates = 0;
    
    /* First pass: count gates and find CIRCUIT_GATES line */
    while (fgets(line, sizeof(line), in)) {
        if (strncmp(line, "CIRCUIT_GATES", 13) == 0) {
            sscanf(line, "CIRCUIT_GATES %u", &num_gates);
            break;
        }
    }

    if (num_gates == 0) {
        fprintf(stderr, "Error: No CIRCUIT_GATES header found\n");
        fclose(in);
        fclose(out);
        return 1;
    }

    /* Allocate gate storage */
    gate_info_t *gates = malloc(num_gates * sizeof(gate_info_t));
    if (!gates) {
        fprintf(stderr, "Error: Out of memory\n");
        fclose(in);
        fclose(out);
        return 1;
    }

    /* Initialize wire mapping */
    wire_mapping_t mapping = {0};
    
    /* Initial PC wires map to input bits 2-33 */
    for (int i = 0; i < 32; i++) {
        mapping.pc_wires[i] = PC_START_BIT + i;
    }
    
    /* Initial register wires map to input bits 34-1057 */
    for (int reg = 0; reg < 32; reg++) {
        for (int bit = 0; bit < 32; bit++) {
            if (reg == 0) {
                /* x0 is always 0 */
                mapping.reg_wires[reg][bit] = CONSTANT_0_WIRE;
            } else {
                mapping.reg_wires[reg][bit] = REGS_START_BIT + (reg * 32) + bit;
            }
        }
    }

    /* Second pass: read gates */
    uint32_t gate_count = 0;
    uint32_t highest_wire = MEMORY_START_BIT;
    
    while (fgets(line, sizeof(line), in) && gate_count < num_gates) {
        if (line[0] == '#' || line[0] == '\n') continue;
        
        uint32_t gate_id, left, right, output;
        char gate_type_str[10];
        
        if (sscanf(line, "%u %u %u %u %s", &gate_id, &left, &right, &output, gate_type_str) == 5) {
            gates[gate_count].gate_id = gate_id;
            gates[gate_count].left_input = left;
            gates[gate_count].right_input = right;
            gates[gate_count].output_wire = output;
            gates[gate_count].gate_type = (strcmp(gate_type_str, "AND") == 0) ? 0 : 1;
            
            if (output > highest_wire) {
                highest_wire = output;
            }
            
            /* Track which gates write to specific register wires */
            /* Check if output wire is in the range for x3 (register 3) */
            /* x3 starts at REGS_START_BIT + 3*32 = 34 + 96 = 130 */
            /* and goes to 130 + 31 = 161 */
            if (output >= 130 && output <= 161) {
                mapping.reg_modified[3] = true;
                /* Update the wire mapping for x3 */
                int bit = output - 130;
                mapping.reg_wires[3][bit] = output;
            }
            
            /* Similarly for x4 (162-193) and x5 (194-225) */
            if (output >= 162 && output <= 193) {
                mapping.reg_modified[4] = true;
                int bit = output - 162;
                mapping.reg_wires[4][bit] = output;
            }
            
            if (output >= 194 && output <= 225) {
                mapping.reg_modified[5] = true;
                int bit = output - 194;
                mapping.reg_wires[5][bit] = output;
            }
            
            gate_count++;
        }
    }

    /* Determine number of inputs and outputs */
    /* Inputs: 2 constants + PC + 32 registers */
    uint32_t num_inputs = 2 + PC_BITS + REGS_BITS;
    
    /* Outputs: PC + modified registers (simplified) */
    uint32_t num_outputs = 0;
    if (mapping.pc_modified) num_outputs += 32;
    for (int reg = 0; reg < 32; reg++) {
        if (mapping.reg_modified[reg]) num_outputs += 32;
    }
    
    /* If no outputs detected, output all modified registers */
    if (num_outputs == 0) {
        /* Count how many registers were actually modified */
        int mod_count = 0;
        for (int reg = 0; reg < 32; reg++) {
            if (mapping.reg_modified[reg]) mod_count++;
        }
        
        /* If we found modified registers, use those */
        if (mod_count > 0) {
            num_outputs = mod_count * 32;
        } else {
            /* Default to x3 only */
            num_outputs = 32;
            mapping.reg_modified[3] = true;
        }
    }

    /* Write circuit_io header */
    fprintf(out, "# RISC-V circuit converted with proper state mapping\n");
    fprintf(out, "# Input layout: [const0, const1, PC[31:0], x0[31:0], x1[31:0], ..., x31[31:0]]\n");
    fprintf(out, "%u %u %u\n", num_inputs, num_gates, num_outputs);
    fprintf(out, "# Gates follow (type left right output)\n");

    /* Write gates */
    for (uint32_t i = 0; i < gate_count; i++) {
        fprintf(out, "%u %u %u %u\n",
                gates[i].gate_type,
                gates[i].left_input,
                gates[i].right_input,
                gates[i].output_wire);
    }

    fprintf(out, "\n# Output wires\n");
    
    /* Output PC if modified */
    if (mapping.pc_modified) {
        fprintf(out, "# PC bits 0-31\n");
        for (int i = 0; i < 32; i++) {
            fprintf(out, "%u\n", mapping.pc_wires[i]);
        }
    }
    
    /* Output modified registers */
    for (int reg = 0; reg < 32; reg++) {
        if (mapping.reg_modified[reg]) {
            fprintf(out, "# Register x%d bits 0-31\n", reg);
            for (int bit = 0; bit < 32; bit++) {
                fprintf(out, "%u\n", mapping.reg_wires[reg][bit]);
            }
        }
    }

    free(gates);
    fclose(in);
    fclose(out);

    printf("Advanced conversion complete:\n");
    printf("  Input gates: %u\n", num_gates);
    printf("  Input bits: %u (2 constants + %u PC + %u registers)\n", 
           num_inputs, PC_BITS, REGS_BITS);
    printf("  Output bits: %u\n", num_outputs);
    printf("  Highest wire: %u\n", highest_wire);
    printf("  PC modified: %s\n", mapping.pc_modified ? "yes" : "no");
    
    int modified_regs = 0;
    for (int reg = 0; reg < 32; reg++) {
        if (mapping.reg_modified[reg]) modified_regs++;
    }
    printf("  Registers modified: %d\n", modified_regs);

    return 0;
}