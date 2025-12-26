# RISC-V Integration Examples

This document shows how to use the RISC-V to Gate Computer integration.

## Prerequisites

1. Build gate_computer and RISC-V compiler:
```bash
cd build && make -j$(nproc) && cd ..
cd modules/riscv_compiler/build && make -j$(nproc) && cd ../../..
```

2. Build the converter tool:
```bash
gcc -o tools/riscv_to_circuit_text tools/riscv_to_circuit_text.c
```

## Example 1: Simple RISC-V Instructions

The `simple_riscv_demo` creates a circuit with ADD, XOR, and AND instructions:

```bash
# Generate circuit
cd modules/riscv_compiler/build
./simple_riscv_demo
# Creates: riscv_circuit.txt (288 gates)

# Convert to gate_computer format
cd ../../..
./tools/riscv_to_circuit_text modules/riscv_compiler/build/riscv_circuit.txt simple.circuit

# Run in gate_computer (with zeros)
./build/bin/gate_computer --load-circuit simple.circuit --input $(python3 -c "print('00' * 128)")
# Result: 00000000
```

## Example 2: Getting Started Demo

A more complex example with multiple instructions:

```bash
# Generate circuit
cd modules/riscv_compiler/build
./getting_started
# Creates: getting_started.circuit (1440 gates)

# Convert and run
cd ../../..
./tools/riscv_to_circuit_text modules/riscv_compiler/build/getting_started.circuit demo.circuit
./build/bin/gate_computer --load-circuit demo.circuit --input $(python3 -c "print('00' * 128)") --dump-stats

# Shows:
# Circuit info: 1058 inputs, 96 outputs, 1440 gates, 97 layers
# Registers modified: 3 (x3, x4, x5)
```

## Input Format

RISC-V circuits expect 1058 bits of input:
- Bits 0-1: Constants (0 and 1)
- Bits 2-33: Program Counter (PC)
- Bits 34-1057: Registers x0-x31 (32 registers × 32 bits)

To create custom inputs, use the provided Python helper:

```python
# make_riscv_input.py
#!/usr/bin/env python3
data = bytearray(133)
data[0] |= 0x02  # Set bit 1 (constant 1)

def set_register(data, reg_num, value):
    start_bit = 34 + (reg_num * 32)
    for i in range(32):
        if value & (1 << i):
            bit_pos = start_bit + i
            byte_idx = bit_pos // 8
            bit_in_byte = bit_pos % 8
            data[byte_idx] |= (1 << bit_in_byte)

set_register(data, 1, 5)   # x1 = 5
set_register(data, 2, 3)   # x2 = 3
print(data.hex())
```

## Known Limitations

1. **Input Alignment**: RISC-V uses 1058 bits (132.25 bytes). Gate computer expects even hex chars, causing "input too large" errors. Workaround: pad to 133 bytes.

2. **Output Interpretation**: The converter outputs modified register values. You need to know which registers were modified to interpret results.

3. **Memory Operations**: Not yet supported in the converter.

## Next Steps

- Compile actual C programs using `compile_to_circuit.sh`
- Generate zero-knowledge proofs with `--prove`
- Test with more complex programs (fibonacci, SHA256, etc.)