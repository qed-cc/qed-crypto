# Circuit Engine

A circuit-based implementation of cryptographic primitives and other computational operations for the Gate Computer framework.

## Features

- SHA3-256 circuit generation and evaluation
- Support for standard FIPS 202 compliant SHA3 operations
- Optimized gate-based implementation

## Dependencies

- circuit_io: For circuit input/output operations
- circuit_evaluator: For circuit evaluation

## Usage

```c
#include <circuit_engine.h>

// Generate a SHA3-256 circuit
circuit_t* circuit = generate_sha3_circuit(SHA3_256);

// Input data
const uint8_t input[] = "abc";
uint8_t output[32] = {0};

// Evaluate the circuit
bool success = evaluate_sha3_circuit(circuit, input, sizeof(input) - 1, output);

// Free the circuit when done
free(circuit);
```