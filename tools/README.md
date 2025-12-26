# Gate Computer Tools

This directory contains utility tools for the Gate Computer project.

## RISC-V Circuit Converter

### riscv_to_circuit_text.c

Converts RISC-V compiler output format to circuit_io text format that gate_computer can load.

**Features:**
- Proper RISC-V state mapping (constants, PC, registers)
- Automatic detection of modified registers
- Handles wire mapping conventions correctly

**Usage:**
```bash
# Compile the converter
gcc -o riscv_to_circuit_text riscv_to_circuit_text.c

# Convert a RISC-V circuit
./riscv_to_circuit_text input.circuit output.circuit

# Example output:
# Advanced conversion complete:
#   Input gates: 1440
#   Input bits: 1058 (2 constants + 32 PC + 1024 registers)
#   Output bits: 96
#   Registers modified: 3
```

**Input/Output Format:**
- Input: RISC-V compiler text format with CIRCUIT_GATES header
- Output: circuit_io text format with proper comments to avoid parser issues

### riscv_to_circuit_text_basic.c

Basic version of the converter (kept for reference). Use the main version for production.

## Other Tools

### convert_circuit

Binary circuit format converter (original tool).

### riscv_to_text_skeleton.c

Template for creating custom circuit converters.