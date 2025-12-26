# Gate Circuit Format Specification v1.0

## Overview

This document specifies the binary format used for gate circuits in the Gate Computer system. All circuits (SHA3, RISC-V compiled, custom) must follow this format for compatibility.

## Binary Format

### File Structure
```
[Header]
[Gate Array]
[Metadata (optional)]
```

### Header (16 bytes)
```c
struct circuit_header {
    uint32_t magic;         // 0x5BA5EC47 ('GATE' encoded)
    uint32_t version;       // Format version (currently 1)
    uint32_t num_inputs;    // Total input bits
    uint32_t num_outputs;   // Total output bits
    uint32_t num_gates;     // Number of gates
    uint32_t metadata_offset; // Offset to metadata (0 if none)
};
```

### Gate Format (13 bytes per gate)
```c
struct gate {
    uint32_t left_input;    // Wire index for left input
    uint32_t right_input;   // Wire index for right input  
    uint32_t output;        // Wire index for output
    uint8_t  type;          // Gate type: 0=AND, 1=XOR
};
```

### Wire Indexing Convention

Wires are indexed as follows:
- **0**: Reserved (unused)
- **1**: Constant 0 (false)
- **2**: Constant 1 (true)
- **3 to (num_inputs+2)**: Input bits
- **(num_inputs+3) and up**: Gate outputs

### Gate Types
- `0x00`: AND gate
- `0x01`: XOR gate
- Future: `0x02`: OR, `0x03`: NOT, etc.

## Examples

### Minimal Circuit (XOR of two inputs)
```
Header:
  magic: 0x5BA5EC47
  version: 1
  num_inputs: 2
  num_outputs: 1
  num_gates: 1
  metadata_offset: 0

Gates:
  Gate 0: left=3, right=4, output=5, type=XOR
```

### SHA3-256 Circuit
```
Header:
  magic: 0x5BA5EC47
  version: 1
  num_inputs: 512    // 512-bit input
  num_outputs: 256   // 256-bit output
  num_gates: 192086  // Actual SHA3 gate count
  metadata_offset: 0

Gates:
  [192086 gates implementing SHA3-256]
```

## Reading Circuits

```c
circuit_t* load_circuit(const char* filename) {
    FILE* f = fopen(filename, "rb");
    
    // Read header
    circuit_header_t header;
    fread(&header, sizeof(header), 1, f);
    
    // Validate magic
    if (header.magic != 0x5BA5EC47) {
        error("Invalid circuit file");
    }
    
    // Allocate circuit
    circuit_t* circuit = malloc(sizeof(circuit_t));
    circuit->num_inputs = header.num_inputs;
    circuit->num_outputs = header.num_outputs;
    circuit->num_gates = header.num_gates;
    
    // Read gates
    circuit->gates = malloc(header.num_gates * sizeof(gate_t));
    fread(circuit->gates, sizeof(gate_t), header.num_gates, f);
    
    fclose(f);
    return circuit;
}
```

## Writing Circuits

```c
void save_circuit(circuit_t* circuit, const char* filename) {
    FILE* f = fopen(filename, "wb");
    
    // Write header
    circuit_header_t header = {
        .magic = 0x5BA5EC47,
        .version = 1,
        .num_inputs = circuit->num_inputs,
        .num_outputs = circuit->num_outputs,
        .num_gates = circuit->num_gates,
        .metadata_offset = 0
    };
    fwrite(&header, sizeof(header), 1, f);
    
    // Write gates
    fwrite(circuit->gates, sizeof(gate_t), circuit->num_gates, f);
    
    fclose(f);
}
```

## Extended Format (v2 proposal)

For future expansion:

```c
struct circuit_metadata {
    char name[64];              // Circuit name
    char description[256];      // Human-readable description
    uint32_t num_public_inputs; // Public input count
    uint32_t num_private_inputs;// Private input count
    uint32_t max_width;         // Maximum circuit width
    uint32_t depth;             // Circuit depth
    uint8_t hash[32];           // SHA256 of circuit
};
```

## Validation Rules

1. **Wire indices must be valid**:
   - Input wires: 3 to (num_inputs + 2)
   - Gate outputs: Sequential starting at (num_inputs + 3)

2. **No circular dependencies**:
   - Gate inputs must come from lower-indexed gates

3. **Output wires must exist**:
   - The last `num_outputs` gates should produce the outputs

## RISC-V Compiler Output Format

The RISC-V compiler produces circuits following this exact format:

```c
// Input layout for RISC-V circuits:
// Bits 0-1: Constants (0, 1)
// Bits 2-33: Program Counter (32 bits)
// Bits 34-1057: Registers (32 registers × 32 bits)
// Bits 1058+: Memory (configurable size)
```

## Tools

### Circuit Inspector
```bash
# Show circuit statistics
./tools/circuit_info circuit.bin

# Validate circuit structure  
./tools/circuit_validate circuit.bin

# Convert to human-readable format
./tools/circuit_dump circuit.bin > circuit.txt
```

### Circuit Converter
```bash
# Convert from RISC-V compiler format
./tools/convert_riscv output.circuit gate_circuit.bin

# Convert from other formats
./tools/convert_bristol bristol.txt gate_circuit.bin
```

## Best Practices

1. **Always validate** circuits after loading
2. **Use streaming** for large circuits (>1M gates)
3. **Compress** circuits for storage (gzip works well)
4. **Cache** frequently used circuits
5. **Version** your circuits with metadata

## FAQ

**Q: Why 13 bytes per gate instead of 12?**
A: The extra byte for gate type allows future expansion to 256 gate types.

**Q: How are multi-bit operations handled?**
A: As collections of single-bit gates. A 32-bit adder uses ~224 individual gates.

**Q: Can circuits have multiple outputs?**
A: Yes, the last `num_outputs` gate outputs are the circuit outputs.

**Q: Is the format endian-sensitive?**
A: Yes, little-endian is assumed. Use conversion tools for big-endian systems.