# Formal Verification Plan for BaseFold Verifier Circuit

## Overview

The BaseFold verifier circuit has ~846 million gates, making direct formal verification challenging. However, we can apply modular verification techniques.

## Current Issues to Fix First

### 1. Critical Bugs
- **GF(2^128) reduction polynomial**: Uses wrong positions for reduction
- **SHA3-256**: Completely inadequate implementation 
- **Proof parsing**: Not implemented at all
- **FRI round consistency**: Missing actual verification logic

### 2. Missing Components
- Proper Keccak-f[1600] permutation
- Proof deserialization 
- Merkle position calculations
- Error propagation

## Formal Verification Approach

### 1. Modular Verification Strategy

#### a) GF(2^128) Arithmetic Module
```
Properties to verify:
- Addition is commutative: a + b = b + a
- Addition is associative: (a + b) + c = a + (b + c)
- Multiplication is associative: (a * b) * c = a * (b * c)
- Distributivity: a * (b + c) = (a * b) + (a * c)
- Reduction correctness: x^128 ≡ x^7 + x^2 + x + 1 (mod p(x))
```

Tools: 
- SMT solver (Z3/CVC5) for algebraic properties
- Bounded model checking for specific test vectors

#### b) SHA3-256 Module
```
Properties to verify:
- Keccak permutation is bijective
- Round constants are correct
- Padding follows SHA3 spec
- Output matches test vectors from NIST
```

Tools:
- SAT solver for permutation properties
- Equivalence checking against reference implementation

#### c) Merkle Tree Verification Module
```
Properties to verify:
- Path reconstruction produces correct root
- 4-ary tree indexing is correct
- Domain separators prevent collision attacks
```

Tools:
- Inductive proof for tree properties
- Model checking for path verification

#### d) Sumcheck Protocol Module
```
Properties to verify:
- g(0) + g(1) = claimed_sum for all valid polynomials
- Polynomial evaluation is correct
- Challenge incorporation preserves soundness
```

Tools:
- Symbolic execution for polynomial arithmetic
- Probabilistic verification of soundness

#### e) FRI Protocol Module
```
Properties to verify:
- Folding preserves polynomial degree
- Query generation is deterministic
- Consistency checks are sound
```

Tools:
- Abstract interpretation for folding
- Model checking for protocol flow

### 2. Compositional Verification

Once modules are verified, prove:
1. **Data flow correctness**: Output of one module correctly feeds into next
2. **Transcript consistency**: Fiat-Shamir challenges are deterministic
3. **Error propagation**: Any failed check results in output 0

### 3. Circuit-Specific Properties

```coq
(* Coq specification example *)
Definition verifier_soundness : Prop :=
  forall (proof : list bool) (circuit : Circuit),
    valid_proof proof circuit = false ->
    circuit_output (verifier_circuit proof) = 0.

Definition verifier_completeness : Prop :=
  forall (proof : list bool) (circuit : Circuit),
    valid_proof proof circuit = true ->
    circuit_output (verifier_circuit proof) = 1.
```

## Implementation Plan

### Phase 1: Fix Critical Bugs
1. Implement correct GF(2^128) reduction
2. Add complete SHA3-256 implementation
3. Implement proof parsing logic
4. Complete FRI verification logic

### Phase 2: Unit Testing
1. Test each module against known vectors
2. Differential testing against C implementation
3. Property-based testing with QuickCheck

### Phase 3: Formal Methods
1. Extract modules to formal specification language
2. Prove properties using appropriate tools
3. Compose proofs for full system

### Phase 4: Circuit Optimization
1. Reduce gate count where possible
2. Optimize critical paths
3. Minimize wire usage

## Tools and Frameworks

### For Circuit Verification
- **ABC**: Academic circuit verification tool
- **Yosys**: Open source circuit synthesis/verification
- **Z3**: SMT solver for arithmetic properties
- **Cryptol**: Domain-specific language for crypto verification

### For Protocol Verification
- **ProVerif**: Cryptographic protocol verifier
- **Tamarin**: Security protocol verification
- **EasyCrypt**: Computer-aided cryptographic proofs

### For Implementation
- **CBMC**: Bounded model checker for C
- **Frama-C**: Framework for C program analysis
- **VeriFast**: Modular program verifier

## Example: Verifying GF128 Multiplication

```c
// Specification in ACSL (ANSI/ISO C Specification Language)
/*@ 
  @ requires \valid_read(a + (0..127)) && \valid_read(b + (0..127));
  @ requires \valid(out + (0..127));
  @ ensures \forall integer i; 0 <= i < 128 ==> 
  @   out[i] == gf128_mul_bit(a, b, i);
  @ assigns out[0..127];
  @*/
void gf128_mul_circuit_verified(
    circuit_builder_t* builder,
    const uint32_t a[128], 
    const uint32_t b[128], 
    uint32_t out[128]
);
```

## Estimated Effort

1. **Bug fixes**: 2-3 weeks
2. **Unit testing**: 1-2 weeks  
3. **Formal specification**: 3-4 weeks
4. **Verification proofs**: 6-8 weeks
5. **Integration**: 2-3 weeks

Total: ~3-4 months for full formal verification

## Conclusion

While the full circuit is too large for monolithic formal verification, a modular approach is feasible. The most critical step is fixing the current implementation bugs, particularly in SHA3 and proof parsing. Once correct, formal methods can provide high assurance of the verifier's soundness and completeness properties.