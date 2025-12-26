# Gate Computer Examples

This directory contains examples demonstrating how to build and evaluate circuits using the Gate Computer.

## Available Examples

### 1. Direct Circuit Example (`direct_circuit/`)

Demonstrates creating and evaluating circuits using the low-level circuit evaluator API:

- Simple XOR gate circuit
- Half adder circuit (sum and carry)
- Full adder circuit (with carry-in and carry-out)

This example shows how to manually specify gates and wires for complete control over circuit design.

### 2. Basic Circuit Example (`basic_circuit/`)

Demonstrates using the higher-level circuit generator API for more complex circuits:

- XOR gate circuit
- Half adder
- Full adder

**Note**: This example currently has issues with the circuit_generator's gate capacity that are being addressed.

## Building and Running Examples

### Build All Examples

```bash
cd /path/to/gate_computer
mkdir -p build && cd build
cmake ..
make
```

### Build a Specific Example

```bash
# From the build directory
cmake --build . --target direct_circuit
```

### Run Examples

```bash
# From the build directory
./bin/direct_circuit
./bin/basic_circuit  # Once fixed
```

## Circuit Design Overview

### Wire IDs

- **0-1**: Constants (0 and 1)
- **2 to N+1**: External inputs
- **N+2 and above**: Gate outputs

### Gate Types

- **AND**: Logical AND operation (type 0)
- **XOR**: Logical XOR operation (type 1)

### Circuit Creation Steps

1. Initialize a circuit with number of inputs, gates, and outputs
2. Add gates to the circuit
3. Specify output wires
4. Prepare circuit for evaluation
5. Initialize wire state and set inputs
6. Evaluate circuit
7. Read output values

See the example code for implementation details.