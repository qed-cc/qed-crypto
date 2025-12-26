# Formal Specifications for BaseFold Verifier Circuit

## Overview

This directory contains formal specifications for the key components of the BaseFold verifier circuit. Each specification is written in a language suitable for formal verification tools.

## Specifications

### 1. GF(2^128) Arithmetic (`gf128_spec.v`)
- **Language**: Verilog/SystemVerilog
- **Tool**: SymbiYosys, Yosys-SMTBMC
- **Properties Verified**:
  - Addition commutativity and associativity
  - Zero identity and self-cancellation
  - Multiplication by 0 and 1
  - Reduction polynomial correctness
- **Usage**:
  ```bash
  sby -f gf128_formal.sby
  ```

### 2. SHA3-256 Hash Function (`sha3_spec.tla`)
- **Language**: TLA+ (Temporal Logic of Actions)
- **Tool**: TLC Model Checker
- **Properties Verified**:
  - State machine correctness
  - Termination guarantee
  - Output length correctness
  - Phase ordering (absorb before squeeze)
  - Determinism
- **Usage**:
  ```bash
  tlc SHA3Spec.tla
  ```

### 3. Sumcheck Protocol (`sumcheck_spec.coq`)
- **Language**: Coq
- **Tool**: Coq Proof Assistant
- **Properties Verified**:
  - Round verification correctness
  - Soundness theorem
  - Completeness theorem
  - Example instantiation
- **Usage**:
  ```bash
  coqc sumcheck_spec.coq
  ```

### 4. FRI Protocol (`fri_spec.lean`)
- **Language**: Lean 4
- **Tool**: Lean 4 Theorem Prover
- **Properties Verified**:
  - Folding operation correctness
  - Query verification
  - Soundness and completeness
  - Circuit implementation correctness
- **Usage**:
  ```bash
  lean --run fri_spec.lean
  ```

### 5. Merkle Trees (`merkle_spec.why`)
- **Language**: Why3
- **Tool**: Why3 Verification Platform
- **Properties Verified**:
  - Tree well-formedness
  - Path verification soundness
  - Collision resistance
  - 4-ary tree structure
- **Usage**:
  ```bash
  why3 prove merkle_spec.why
  ```

## Verification Strategy

### Modular Approach
Each component is verified independently:
1. **Arithmetic Layer**: GF(2^128) operations
2. **Cryptographic Layer**: SHA3 hashing
3. **Protocol Layer**: Sumcheck and FRI
4. **Data Structure Layer**: Merkle trees

### Composition
After verifying components individually:
1. Verify interfaces between components
2. Check data flow correctness
3. Prove end-to-end properties

## Key Properties

### Security Properties
- **Soundness**: Invalid proofs are rejected with overwhelming probability
- **Completeness**: Valid proofs are always accepted
- **Zero-knowledge**: No information leaks (where applicable)

### Functional Properties
- **Determinism**: Same input produces same output
- **Termination**: All algorithms complete in finite time
- **Correctness**: Output matches specification

## Tool Installation

### SymbiYosys (for Verilog)
```bash
pip install sby
# Also need Yosys and SMT solver (e.g., Z3)
```

### TLA+ (TLC)
```bash
# Download from https://lamport.azurewebsites.net/tla/tools.html
java -jar tla2tools.jar SHA3Spec.tla
```

### Coq
```bash
# Install via OPAM
opam install coq
```

### Lean 4
```bash
# Install from https://leanprover.github.io/
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

### Why3
```bash
# Install via OPAM
opam install why3 why3-ide
```

## Formal Verification Workflow

1. **Write Specification**: Define properties in formal language
2. **Prove Properties**: Use automated or interactive provers
3. **Extract Verified Code**: Generate implementation from proof
4. **Test Against Circuit**: Ensure circuit matches specification

## Current Status

| Component | Specification | Proofs | Extraction |
|-----------|--------------|--------|------------|
| GF(2^128) | ✅ Complete | 🔧 Partial | ❌ TODO |
| SHA3-256 | ✅ Complete | 🔧 Partial | ❌ TODO |
| Sumcheck | ✅ Complete | 🔧 Partial | ❌ TODO |
| FRI | ✅ Complete | 🔧 Partial | ❌ TODO |
| Merkle | ✅ Complete | 🔧 Partial | ❌ TODO |

## Next Steps

1. **Complete Proofs**: Fill in `sorry` and `Admitted` sections
2. **Add Circuit Properties**: Verify gate-level implementations
3. **Compositional Verification**: Prove component interactions
4. **Performance Analysis**: Verify complexity bounds
5. **Code Extraction**: Generate verified C code

## Example: Verifying GF128 Multiplication

```verilog
// Run formal verification
module test_gf128_mul_formal;
    reg [127:0] a, b;
    wire [127:0] result;
    
    gf128_mul dut(.a(a), .b(b), .result(result));
    
    // Property: Multiplication by 1
    always @(*) begin
        if (a == 128'h1)
            assert(result == b);
        if (b == 128'h1)
            assert(result == a);
    end
endmodule
```

## References

1. [BaseFold Paper](https://eprint.iacr.org/2023/1939)
2. [FRI Protocol](https://eccc.weizmann.ac.il/report/2017/134/)
3. [Sumcheck Protocol](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf)
4. [SHA3 Standard](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf)