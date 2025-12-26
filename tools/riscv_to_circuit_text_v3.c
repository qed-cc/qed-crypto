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
 * This v3 converter improves on previous versions by:
 * - Automatic detection of modified state components
 * - More accurate wire tracking
 * - Flexible output configuration
 * - Better error handling and reporting
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

/* Enhanced wire mapping with better tracking */
typedef struct {
    uint32_t pc_wires[32];      /* PC bit wires */
    uint32_t reg_wires[32][32]; /* Register bit wires [reg][bit] */
    bool pc_modified;
    bool reg_modified[32];
    uint32_t highest_wire;
    uint32_t num_output_wires;
    uint32_t *output_wires;     /* Dynamic list of output wires */
} wire_mapping_t;

/* Enhanced output wire detection */
static void detect_output_wires(gate_info_t *gates, uint32_t num_gates, wire_mapping_t *mapping) {
    /* Build wire usage map */
    bool *wire_is_output = calloc(mapping->highest_wire + 1, sizeof(bool));
    bool *wire_is_input = calloc(mapping->highest_wire + 1, sizeof(bool));
    
    if (!wire_is_output || !wire_is_input) {
        fprintf(stderr, "Error: Out of memory for wire tracking\n");
        free(wire_is_output);
        free(wire_is_input);
        return;
    }
    
    /* Mark all wires that are inputs to gates */
    for (uint32_t i = 0; i < num_gates; i++) {
        wire_is_input[gates[i].left_input] = true;
        wire_is_input[gates[i].right_input] = true;
    }
    
    /* Mark all wires that are outputs from gates */
    for (uint32_t i = 0; i < num_gates; i++) {
        wire_is_output[gates[i].output_wire] = true;
    }
    
    /* Count output wires that are not used as inputs (final outputs) */
    uint32_t output_count = 0;
    for (uint32_t wire = 0; wire <= mapping->highest_wire; wire++) {
        if (wire_is_output[wire] && !wire_is_input[wire]) {
            output_count++;
        }
    }
    
    /* Allocate and populate output wire list */
    mapping->output_wires = malloc(output_count * sizeof(uint32_t));
    mapping->num_output_wires = 0;
    
    if (mapping->output_wires) {
        for (uint32_t wire = 0; wire <= mapping->highest_wire; wire++) {
            if (wire_is_output[wire] && !wire_is_input[wire]) {
                mapping->output_wires[mapping->num_output_wires++] = wire;
            }
        }
    }
    
    /* Analyze which registers/PC are modified */
    for (uint32_t i = 0; i < mapping->num_output_wires; i++) {
        uint32_t wire = mapping->output_wires[i];
        
        /* Check if wire is in PC range */
        if (wire >= PC_START_BIT && wire < PC_START_BIT + PC_BITS) {
            mapping->pc_modified = true;
            int bit = wire - PC_START_BIT;
            mapping->pc_wires[bit] = wire;
        }
        
        /* Check if wire is in register range */
        if (wire >= REGS_START_BIT && wire < REGS_START_BIT + REGS_BITS) {
            int wire_offset = wire - REGS_START_BIT;
            int reg = wire_offset / 32;
            int bit = wire_offset % 32;
            
            if (reg >= 0 && reg < 32) {
                mapping->reg_modified[reg] = true;
                mapping->reg_wires[reg][bit] = wire;
            }
        }
    }
    
    free(wire_is_output);
    free(wire_is_input);
}

int main(int argc, char *argv[]) {
    if (argc < 3 || argc > 4) {
        fprintf(stderr, "Usage: %s <input_file> <output_file> [--minimal-output]\n", argv[0]);
        fprintf(stderr, "Converts RISC-V compiler circuit format to circuit_io text format\n");
        fprintf(stderr, "with automatic state mapping and output detection\n");
        fprintf(stderr, "\n");
        fprintf(stderr, "Options:\n");
        fprintf(stderr, "  --minimal-output  Only output actually modified registers\n");
        return 1;
    }

    bool minimal_output = false;
    if (argc == 4 && strcmp(argv[3], "--minimal-output") == 0) {
        minimal_output = true;
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
    mapping.highest_wire = MEMORY_START_BIT;
    
    /* Initialize PC wires map to input bits 2-33 */
    for (int i = 0; i < 32; i++) {
        mapping.pc_wires[i] = PC_START_BIT + i;
    }
    
    /* Initialize register wires map to input bits 34-1057 */
    for (int reg = 0; reg < 32; reg++) {
        for (int bit = 0; bit < 32; bit++) {
            if (reg == 0) {
                /* x0 is always 0 (hardwired to constant) */
                mapping.reg_wires[reg][bit] = CONSTANT_0_WIRE;
            } else {
                mapping.reg_wires[reg][bit] = REGS_START_BIT + (reg * 32) + bit;
            }
        }
    }

    /* Second pass: read gates */
    uint32_t gate_count = 0;
    
    while (fgets(line, sizeof(line), in) && gate_count < num_gates) {
        if (line[0] == '#' || line[0] == '\n' || strlen(line) < 5) continue;
        
        uint32_t gate_id, left, right, output;
        char gate_type_str[10];
        
        if (sscanf(line, "%u %u %u %u %s", &gate_id, &left, &right, &output, gate_type_str) == 5) {
            gates[gate_count].gate_id = gate_id;
            gates[gate_count].left_input = left;
            gates[gate_count].right_input = right;
            gates[gate_count].output_wire = output;
            gates[gate_count].gate_type = (strcmp(gate_type_str, "AND") == 0) ? 0 : 1;
            
            if (output > mapping.highest_wire) {
                mapping.highest_wire = output;
            }
            
            gate_count++;
        }
    }

    /* Detect output wires automatically */
    detect_output_wires(gates, gate_count, &mapping);

    /* Determine number of inputs and outputs */
    uint32_t num_inputs = 2 + PC_BITS + REGS_BITS; /* Constants + PC + all registers */
    
    uint32_t num_outputs;
    if (minimal_output) {
        /* Only output actually modified components */
        num_outputs = mapping.num_output_wires;
    } else {
        /* Output full state of modified components */
        num_outputs = 0;
        if (mapping.pc_modified) num_outputs += 32;
        for (int reg = 0; reg < 32; reg++) {
            if (mapping.reg_modified[reg]) num_outputs += 32;
        }
        
        /* If no outputs detected, fall back to direct wire mapping */
        if (num_outputs == 0) {
            num_outputs = mapping.num_output_wires;
        }
    }

    /* Write circuit_io header with comment barrier */
    fprintf(out, "# RISC-V circuit converted with v3 converter\n");
    fprintf(out, "# Input layout: [const0, const1, PC[31:0], x0[31:0], x1[31:0], ..., x31[31:0]]\n");
    fprintf(out, "# Auto-detected: PC_mod=%s, Regs_mod=", mapping.pc_modified ? "yes" : "no");
    
    for (int reg = 0; reg < 32; reg++) {
        if (mapping.reg_modified[reg]) {
            fprintf(out, "x%d ", reg);
        }
    }
    fprintf(out, "\n");
    
    fprintf(out, "%u %u %u\n", num_inputs, gate_count, num_outputs);
    fprintf(out, "# Circuit format barrier - prevents fscanf cross-reading\n");

    /* Write gates in circuit_io format */
    for (uint32_t i = 0; i < gate_count; i++) {
        fprintf(out, "%u %u %u %u\n",
                gates[i].gate_type,
                gates[i].left_input,
                gates[i].right_input,
                gates[i].output_wire);
    }

    fprintf(out, "\n# Output wires (auto-detected)\n");
    
    if (minimal_output || num_outputs == mapping.num_output_wires) {
        /* Direct wire output */
        for (uint32_t i = 0; i < mapping.num_output_wires; i++) {
            fprintf(out, "%u\n", mapping.output_wires[i]);
        }
    } else {
        /* Full state output for modified components */
        if (mapping.pc_modified) {
            fprintf(out, "# PC bits 0-31\n");
            for (int i = 0; i < 32; i++) {
                fprintf(out, "%u\n", mapping.pc_wires[i]);
            }
        }
        
        for (int reg = 0; reg < 32; reg++) {
            if (mapping.reg_modified[reg]) {
                fprintf(out, "# Register x%d bits 0-31\n", reg);
                for (int bit = 0; bit < 32; bit++) {
                    fprintf(out, "%u\n", mapping.reg_wires[reg][bit]);
                }
            }
        }
    }

    /* Cleanup and report */
    free(gates);
    free(mapping.output_wires);
    fclose(in);
    fclose(out);

    printf("V3 conversion complete:\n");
    printf("  Input gates: %u\n", gate_count);
    printf("  Input bits: %u (2 constants + %u PC + %u registers)\n", 
           num_inputs, PC_BITS, REGS_BITS);
    printf("  Output bits: %u (%s)\n", num_outputs, 
           minimal_output ? "minimal" : "full state");
    printf("  Highest wire: %u\n", mapping.highest_wire);
    printf("  Output wires detected: %u\n", mapping.num_output_wires);
    printf("  PC modified: %s\n", mapping.pc_modified ? "yes" : "no");
    
    int modified_regs = 0;
    for (int reg = 0; reg < 32; reg++) {
        if (mapping.reg_modified[reg]) {
            printf("  Register x%d: modified\n", reg);
            modified_regs++;
        }
    }
    printf("  Total registers modified: %d\n", modified_regs);

    return 0;
}