/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * make_riscv_input.c - Generate RISC-V state input data for gate_computer circuits
 * 
 * This program creates properly formatted hex input for RISC-V circuits
 * by setting register values and handling the correct bit layout.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <getopt.h>

/* C99-compatible strdup implementation */
static char *my_strdup(const char *s) {
    size_t len = strlen(s) + 1;
    char *dup = malloc(len);
    if (dup) {
        memcpy(dup, s, len);
    }
    return dup;
}

/*
 * RISC-V circuit input layout (1058 bits total):
 * Bits 0-1:     Constants (hardwired to 0, 1)
 * Bits 2-33:    Program Counter (PC, 32 bits) 
 * Bits 34-1057: Registers x0-x31 (32 registers × 32 bits each)
 * Bits 1058+:   Memory (if any)
 */

#define RISCV_NUM_REGISTERS 32
#define RISCV_REGISTER_BITS 32
#define RISCV_PC_BITS 32
#define RISCV_TOTAL_BYTES 133  /* (1058 + 7) / 8 rounded up */

typedef struct {
    uint32_t pc;
    uint32_t registers[RISCV_NUM_REGISTERS];
} riscv_state_t;

static void print_usage(const char *program_name) {
    printf("Usage: %s [options]\n", program_name);
    printf("\n");
    printf("Generate RISC-V circuit input data for gate_computer.\n");
    printf("\n");
    printf("Options:\n");
    printf("  --pc VALUE        Set program counter value (default: 0)\n");
    printf("  --reg xN=VALUE    Set register xN to VALUE (hex or decimal)\n");
    printf("  --example         Show example usage\n");
    printf("  --help            Show this help message\n");
    printf("\n");
    printf("Examples:\n");
    printf("  # All zeros:\n");
    printf("  %s\n", program_name);
    printf("\n");
    printf("  # Set x1=1, x2=2:\n");
    printf("  %s --reg x1=1 --reg x2=2\n", program_name);
    printf("\n");
    printf("  # Set PC and registers:\n");
    printf("  %s --pc 0x1000 --reg x1=0xFF --reg x2=0xAA\n", program_name);
    printf("\n");
    printf("Usage with gate_computer:\n");
    printf("  %s --reg x1=5 --reg x2=3 | ./build/bin/gate_computer --load-circuit circuit.txt --input $(cat)\n", program_name);
}

static int parse_value(const char *str, uint32_t *value) {
    char *endptr;
    
    if (strncmp(str, "0x", 2) == 0 || strncmp(str, "0X", 2) == 0) {
        *value = (uint32_t)strtoul(str, &endptr, 16);
    } else {
        *value = (uint32_t)strtoul(str, &endptr, 10);
    }
    
    return (*endptr == '\0') ? 0 : -1;
}

static int parse_register(const char *reg_spec, int *reg_num, uint32_t *value) {
    if (reg_spec[0] != 'x') {
        return -1;
    }
    
    char *equals = strchr(reg_spec, '=');
    if (!equals) {
        return -1;
    }
    
    *equals = '\0';  /* Temporarily modify string */
    
    /* Parse register number */
    char *endptr;
    long reg = strtol(reg_spec + 1, &endptr, 10);
    if (*endptr != '\0' || reg < 0 || reg >= RISCV_NUM_REGISTERS) {
        *equals = '=';  /* Restore string */
        return -1;
    }
    
    *reg_num = (int)reg;
    
    /* Parse value */
    int result = parse_value(equals + 1, value);
    *equals = '=';  /* Restore string */
    
    return result;
}

/* Helper function to add bits to output */
static void add_bits_to_output(uint8_t *output, int *byte_idx, int *bit_idx, uint32_t value, int num_bits) {
    for (int i = 0; i < num_bits; i++) {
        if (value & (1U << i)) {
            output[*byte_idx] |= (1U << (*bit_idx));
        }
        
        (*bit_idx)++;
        if (*bit_idx == 8) {
            *bit_idx = 0;
            (*byte_idx)++;
        }
    }
}

static void generate_riscv_input(const riscv_state_t *state) {
    uint8_t output[RISCV_TOTAL_BYTES] = {0};
    int byte_idx = 0;
    int bit_idx = 0;
    
    /* Constants (2 bits): wire 0=0, wire 1=1 */
    add_bits_to_output(output, &byte_idx, &bit_idx, 0, 1);  /* Constant 0 */
    add_bits_to_output(output, &byte_idx, &bit_idx, 1, 1);  /* Constant 1 */
    
    /* Program Counter (32 bits) */
    add_bits_to_output(output, &byte_idx, &bit_idx, state->pc, RISCV_PC_BITS);
    
    /* Registers x0-x31 (32 bits each) */
    for (int reg = 0; reg < RISCV_NUM_REGISTERS; reg++) {
        if (reg == 0) {
            /* x0 is hardwired to zero in RISC-V */
            add_bits_to_output(output, &byte_idx, &bit_idx, 0, RISCV_REGISTER_BITS);
        } else {
            add_bits_to_output(output, &byte_idx, &bit_idx, state->registers[reg], RISCV_REGISTER_BITS);
        }
    }
    
    /* Output as hex string */
    for (int i = 0; i < RISCV_TOTAL_BYTES; i++) {
        printf("%02x", output[i]);
    }
    printf("\n");
}

static void show_examples(void) {
    riscv_state_t state = {0};
    
    printf("Examples:\n\n");
    
    printf("# All zeros:\n");
    generate_riscv_input(&state);
    printf("\n");
    
    printf("# Set x1=1, x2=2:\n");
    state.registers[1] = 1;
    state.registers[2] = 2;
    generate_riscv_input(&state);
    printf("\n");
    
    printf("# Set PC=0x1000, x1=0xFFFFFFFF:\n");
    memset(&state, 0, sizeof(state));
    state.pc = 0x1000;
    state.registers[1] = 0xFFFFFFFF;
    generate_riscv_input(&state);
    printf("\n");
}

int main(int argc, char *argv[]) {
    riscv_state_t state = {0};
    int show_help = 0;
    int show_examples_flag = 0;
    
    static struct option long_options[] = {
        {"pc",      required_argument, 0, 'p'},
        {"reg",     required_argument, 0, 'r'},
        {"example", no_argument,       0, 'e'},
        {"help",    no_argument,       0, 'h'},
        {0, 0, 0, 0}
    };
    
    int c;
    while ((c = getopt_long(argc, argv, "p:r:eh", long_options, NULL)) != -1) {
        switch (c) {
        case 'p':
            if (parse_value(optarg, &state.pc) != 0) {
                fprintf(stderr, "Error: Invalid PC value: %s\n", optarg);
                return 1;
            }
            break;
            
        case 'r': {
            int reg_num;
            uint32_t value;
            char *reg_spec = my_strdup(optarg);
            if (parse_register(reg_spec, &reg_num, &value) != 0) {
                fprintf(stderr, "Error: Invalid register spec: %s\n", optarg);
                fprintf(stderr, "Use format: x1=0xFF or x2=42\n");
                free(reg_spec);
                return 1;
            }
            state.registers[reg_num] = value;
            free(reg_spec);
            break;
        }
        
        case 'e':
            show_examples_flag = 1;
            break;
            
        case 'h':
            show_help = 1;
            break;
            
        default:
            fprintf(stderr, "Use --help for usage information.\n");
            return 1;
        }
    }
    
    if (show_help) {
        print_usage(argv[0]);
        return 0;
    }
    
    if (show_examples_flag) {
        show_examples();
        return 0;
    }
    
    /* Generate and output the RISC-V input data */
    generate_riscv_input(&state);
    
    return 0;
}