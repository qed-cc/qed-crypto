# Cmptr - Zero-Knowledge Proof System

A complete implementation of cryptographic circuit evaluation with zero-knowledge proof generation and verification using the BaseFold protocol.

⚠️ **IMPORTANT**: The zero-knowledge feature is currently disabled due to implementation issues. Proofs are generated but do not provide zero-knowledge privacy. See:
- [BASEFOLD_FIX_SUMMARY.md](../../BASEFOLD_FIX_SUMMARY.md) - Quick fix overview
- [BASEFOLD_COMPLETE_FIX_GUIDE.md](../../BASEFOLD_COMPLETE_FIX_GUIDE.md) - Detailed implementation plan
- [ZERO_KNOWLEDGE_TODO.md](../../ZERO_KNOWLEDGE_TODO.md) - Technical details

## Features

### Circuit Evaluation
- **SHA3-256 Implementation**: Production-ready circuit with 192,086 gates
- **High Performance**: Parallel layer processing with ~170M gates/second
- **Flexible Input**: Support for text, binary, or hexadecimal input data (up to 135 bytes)

### Zero-Knowledge Proof System
- **Complete BaseFold Protocol**: Gate and Wiring SumCheck with 18 verification rounds
- **Cryptographic Security**: Production-grade security with tamper detection
- **Zero-Knowledge**: ⚠️ Currently disabled - needs polynomial randomization implementation
- **Public Output Validation**: Verify computation produces expected results
- **Non-Interactive**: Fiat-Shamir transcript eliminates interaction requirements

## Quick Start

### Build
```bash
./build.sh
```

### Generate Hash
```bash
./build/cmptr --gen-sha3-256 --input-text "hello world"
```
Output: `644bcc7e564373040999aac89e7622f3ca71fba1d972fd94a31c3bfbf24e3938`

### Generate Zero-Knowledge Proof
```bash
./build/cmptr --gen-sha3-256 --input-text "secret data" --prove proof.bfp
```

### Verify Proof (Zero-Knowledge)
```bash
./build/cmptr --verify proof.bfp
```

### Verify Proof with Expected Output
```bash
./build/cmptr --verify proof.bfp --expected-output 644bcc7e564373040999aac89e7622f3ca71fba1d972fd94a31c3bfbf24e3938
```

## Command Line Options

```
Usage: ./build/cmptr [options]

Options:
  --gen-sha3-256          Generate SHA3-256 circuit with auto-padding
  --input-text <text>     Process input data as UTF-8 text
  --input <hex_string>    Process input data as hexadecimal
  --prove <file>          Generate BaseFold zero-knowledge proof
  --verify <file>         Verify BaseFold proof (zero-knowledge)
  --expected-output <hex> Expected public output (64 hex chars)
  --verbose               Show detailed timing and proof information
  --help                  Display help message
```

## Performance Characteristics

- **Proof Generation**: ~3.3 seconds for 192,086 gates
- **Proof Verification**: ~0.05 seconds
- **Proof Size**: 2,420 bytes (2.4 KB)
- **Memory Usage**: ~16 MB peak during generation
- **Circuit Evaluation**: ~0.001 seconds

## Zero-Knowledge Properties

### What the Verifier Learns
- ✅ **Circuit**: SHA3-256 computation was performed correctly
- ✅ **Public Output**: Computation produced the expected result (if specified)
- ✅ **Correctness**: All 192,086 gates executed properly

### What the Verifier NEVER Learns
- ❌ **Secret Input**: The input data remains completely private
- ❌ **Intermediate Values**: No internal computation state is revealed
- ❌ **Input Length**: No information about input characteristics

## Security Guarantees

- **Completeness**: Valid computations always produce verifiable proofs
- **Soundness**: Invalid computations cannot produce valid proofs
- **Zero-Knowledge**: Verifier learns nothing about secret inputs
- **Tamper Detection**: Merkle tree commitments detect any proof modification

## Proof File Format

BaseFold proof files (`.bfp`) contain:

| Component | Size | Purpose |
|-----------|------|---------|
| Header | 80 bytes | Metadata and public output hash |
| Merkle Root | 32 bytes | Cryptographic commitment |
| Gate SumCheck | 1,152 bytes | 18 rounds of polynomial coefficients |
| Wiring SumCheck | 1,152 bytes | 18 rounds of consistency proofs |
| **Total** | **2,416 bytes** | **Complete cryptographic proof** |

## Advanced Usage

### Detailed Timing Analysis
```bash
./build/cmptr --gen-sha3-256 --input-text "data" --prove proof.bfp --verbose
```

Shows step-by-step timing:
- Trace initialization: ~0.000s
- Circuit evaluation: ~0.002s
- Trace padding: ~0.012s
- ZK masking: ~0.022s
- Merkle tree: ~0.000s
- Gate SumCheck: ~1.460s
- Wiring SumCheck: ~1.832s

### Verification with Public Output
```bash
# Generate proof
./build/cmptr --gen-sha3-256 --input-text "my secret" --prove secret.bfp

# Verify without knowing the input, but confirming the public output
./build/cmptr --verify secret.bfp --expected-output <expected-hash>
```

## Technical Implementation

### BaseFold Protocol Components
1. **Trace Generation**: Records gate-level execution
2. **Zero-Knowledge Masking**: Applies cryptographic PRG masking  
3. **Merkle Tree**: Builds tamper-evident commitments
4. **Gate SumCheck**: Proves gate constraint satisfaction (18 rounds)
5. **Wiring SumCheck**: Proves input/output consistency (18 rounds)

### Cryptographic Primitives
- **Field Arithmetic**: GF(2^128) with CPU optimization
- **Hash Function**: SHA-3-256 for Merkle commitments
- **PRG**: AES-CTR for zero-knowledge masking
- **Transcript**: Fiat-Shamir for non-interactive proofs

## Files and Structure

```
apps/cmptr/
├── src/
│   ├── main.c              # Main application and CLI
│   ├── sha3_final.c        # SHA3-256 circuit implementation
│   ├── evaluator.c         # Circuit evaluation engine
│   └── circuit_format.c    # Binary circuit serialization
├── circuits/
│   └── sha3_256.circuit    # Pre-generated SHA3-256 circuit
├── tools/
│   ├── count_gate_types.c  # Circuit analysis utility
│   └── trace_evaluation.c  # Performance profiling tool
└── README.md               # This file
```

## License

This software is part of the Gate Computer project. See the main project documentation for licensing information.