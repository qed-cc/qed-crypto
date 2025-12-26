# RISC-V to Gate Computer Integration Guide

## Overview

This guide explains how to integrate RISC-V compiled circuits with the Gate Computer proof system.

## Quick Start

### 1. Compile C Program to Circuit
```bash
cd modules/riscv_compiler
./scripts/compile_to_circuit.sh my_program.c -o my_circuit.bin -m ultra
```

### 2. Generate Proof in Gate Computer
```bash
cd ../..
./build/bin/gate_computer --load-circuit my_circuit.bin --prove proof.bfp
```

### 3. Verify Proof
```bash
./build/bin/gate_computer --verify proof.bfp
```

## Architecture Overview

```
C Program → RISC-V Compiler → Gate Circuit → Gate Computer → ZK Proof
                                     ↓                            ↓
                              .circuit file                  .bfp file
```

## Circuit Format Compatibility

Both systems use the same gate circuit format:
- Magic number: `0x5BA5EC47`
- Gate types: AND (0), XOR (1)
- Wire indexing: Inputs start at 3, outputs sequential

## Memory Modes

The RISC-V compiler supports three memory modes:

### Ultra Mode (Fastest, Limited)
- 8 words of memory
- 2.2K gates per memory operation
- Best for simple computations

```bash
./scripts/compile_to_circuit.sh program.c -o circuit.bin -m ultra
```

### Simple Mode (Balanced)
- 256 words of memory
- 101K gates per memory operation
- Good for moderate programs

```bash
./scripts/compile_to_circuit.sh program.c -o circuit.bin -m simple
```

### Secure Mode (Full zkVM)
- Unlimited memory
- 3.9M gates per memory operation
- SHA3 Merkle proofs

```bash
./scripts/compile_to_circuit.sh program.c -o circuit.bin -m secure
```

## Input Layout

RISC-V circuits have a specific input bit layout:

```
Bit Range     | Purpose
------------- | ------------------
0-1          | Constants (0, 1)
2-33         | Program Counter
34-1057      | Registers (32 × 32-bit)
1058+        | Memory (if used)
```

## Example Programs

### 1. Simple Addition
```c
// add.c
int main() {
    int a = 5;
    int b = 3;
    return a + b;
}
```

Compile and prove:
```bash
cd modules/riscv_compiler
./scripts/compile_to_circuit.sh add.c -o add.circuit -m ultra

cd ../..
./build/bin/gate_computer --load-circuit add.circuit --prove add.proof
```

### 2. Fibonacci
```c
// fib.c
int fibonacci(int n) {
    if (n <= 1) return n;
    return fibonacci(n-1) + fibonacci(n-2);
}

int main() {
    return fibonacci(10);
}
```

### 3. SHA256 in C
```c
// sha256.c
#include "zkvm.h"

int main() {
    uint8_t data[] = "hello world";
    uint8_t hash[32];
    zkvm_sha256(data, sizeof(data)-1, hash);
    return hash[0];
}
```

## Performance Optimization

### 1. Choose the Right Memory Mode
- Use `ultra` for arithmetic-heavy code
- Use `simple` for moderate memory usage
- Use `secure` only when necessary

### 2. Minimize Memory Operations
```c
// Bad: Many memory accesses
for (int i = 0; i < n; i++) {
    sum += array[i];
}

// Better: Register variables
int local_sum = 0;
for (int i = 0; i < n; i++) {
    local_sum += array[i];
}
sum = local_sum;
```

### 3. Use Circuit-Friendly Operations
```c
// Use XOR instead of branching when possible
int max = (a > b) ? a : b;  // Expensive

// Circuit-friendly alternative
int diff = a - b;
int sign = diff >> 31;  // Sign bit
int max = (a & ~sign) | (b & sign);
```

## Debugging

### 1. Check Circuit Statistics
```bash
./build/bin/gate_computer --load-circuit my.circuit --dump-stats
```

### 2. Trace Execution
```bash
# In RISC-V compiler
cd modules/riscv_compiler
./trace_evaluation my_program

# In Gate Computer  
./build/bin/gate_computer --load-circuit my.circuit --trace-eval
```

### 3. Disable ZK for Testing
```bash
./build/bin/gate_computer --load-circuit my.circuit --no-zk
```

## Common Issues

### Circuit Too Large
**Problem**: "Circuit exceeds memory limits"
**Solution**: Use a simpler memory mode or optimize your code

### Invalid Wire Indices
**Problem**: "Wire index out of bounds"
**Solution**: Ensure circuit was compiled with compatible RISC-V compiler version

### Proof Generation Timeout
**Problem**: Proof takes too long
**Solution**: Profile your code and reduce gate count

## Advanced Integration

### Custom Circuit Generator
```c
// In gate_computer main.c
if (strcmp(argv[i], "--gen-riscv") == 0) {
    // Initialize RISC-V compiler
    riscv_compiler_t* compiler = riscv_compiler_create();
    
    // Load ELF file
    riscv_elf_t* elf = riscv_load_elf(argv[++i]);
    
    // Compile to circuit
    circuit = riscv_compile_elf(compiler, elf);
}
```

### Batch Processing
```bash
#!/bin/bash
# Process multiple circuits
for circuit in circuits/*.circuit; do
    echo "Proving $circuit..."
    ./build/bin/gate_computer \
        --load-circuit "$circuit" \
        --prove "${circuit%.circuit}.proof"
done
```

## Future Enhancements

1. **Streaming Circuits**: For circuits too large to fit in memory
2. **Incremental Proofs**: Prove long computations in steps
3. **Public Inputs**: Support mixed public/private inputs
4. **Recursive Proofs**: Prove verification of other proofs

## Resources

- [Circuit Format Specification](CIRCUIT_FORMAT_SPEC.md)
- [RISC-V Compiler Documentation](../modules/riscv_compiler/README.md)
- [BaseFold Protocol Paper](https://eprint.iacr.org/2023/xxx)

## Getting Help

1. Check circuit compatibility: `circuit_validate`
2. Review example programs in `examples/`
3. Enable verbose output: `--verbose`
4. File issues on GitHub with circuit statistics