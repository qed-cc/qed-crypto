/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0 */

#ifndef FORMAL_PROOF_CIRCUITS_H
#define FORMAL_PROOF_CIRCUITS_H

#include <stdint.h>
#include <stdbool.h>

/**
 * @file formal_proof_circuits.h
 * @brief Convert formal proofs into circuits for computational verification
 * 
 * This revolutionary system allows us to:
 * 1. Encode any FOPL statement as a circuit
 * 2. Prove the circuit is satisfied with BaseFold RAA
 * 3. Get cryptographic certainty for mathematical theorems
 */

// Logical connectives as gates
typedef enum {
    LOGIC_VAR,      // Variable/wire
    LOGIC_NOT,      // Negation
    LOGIC_AND,      // Conjunction
    LOGIC_OR,       // Disjunction
    LOGIC_IMPLIES,  // Implication
    LOGIC_IFF,      // Biconditional
    LOGIC_XOR,      // Exclusive or
    LOGIC_FORALL,   // Universal quantifier
    LOGIC_EXISTS,   // Existential quantifier
    LOGIC_PRED,     // Predicate application
    LOGIC_FUNC,     // Function application
    LOGIC_EQ,       // Equality
    LOGIC_LT,       // Less than
    LOGIC_GT        // Greater than
} logic_node_type_t;

// AST node for logical formulas
typedef struct logic_node {
    logic_node_type_t type;
    char* name;                    // For variables/predicates
    struct logic_node* left;       // Left child
    struct logic_node* right;      // Right child
    struct logic_node* quantified; // Variable being quantified
    int arity;                     // For predicates/functions
    struct logic_node** args;      // Arguments for predicates
} logic_node_t;

// Circuit representation
typedef struct {
    int num_inputs;
    int num_outputs;
    int num_gates;
    int num_wires;
    
    // Gate connectivity
    int* gate_type;     // Type of each gate
    int** gate_inputs;  // Input wires for each gate
    int* gate_output;   // Output wire for each gate
    
    // Constraints
    int num_constraints;
    int* constraint_wires;  // Wires that must equal 1
    
    // Witness generation hints
    void* witness_hints;
} proof_circuit_t;

// Proof obligation
typedef struct {
    char* name;
    char* description;
    logic_node_t* formula;
    proof_circuit_t* circuit;
    uint8_t* proof;  // BaseFold RAA proof
    size_t proof_size;
    bool proven;
} proof_obligation_t;

// Theory/Module
typedef struct {
    char* name;
    int num_axioms;
    logic_node_t** axioms;
    int num_definitions;
    logic_node_t** definitions;
    int num_theorems;
    proof_obligation_t** theorems;
} formal_theory_t;

/* ============================================================================
 * Core API
 * ============================================================================ */

// Parse FOPL string to AST
logic_node_t* parse_fopl(const char* formula);

// Compile logical formula to circuit
proof_circuit_t* compile_to_circuit(logic_node_t* formula);

// Generate witness for existential statements
bool generate_witness(proof_circuit_t* circuit, uint8_t* witness);

// Prove circuit satisfaction with BaseFold RAA
bool prove_circuit(proof_circuit_t* circuit, uint8_t* witness, 
                  uint8_t* proof_out, size_t* proof_size);

// Verify a proof
bool verify_proof(proof_circuit_t* circuit, uint8_t* proof, size_t proof_size);

/* ============================================================================
 * High-level proof management
 * ============================================================================ */

// Create a new theory
formal_theory_t* create_theory(const char* name);

// Add axiom to theory
void add_axiom(formal_theory_t* theory, const char* axiom);

// Add definition
void add_definition(formal_theory_t* theory, const char* name, const char* definition);

// Add theorem to prove
proof_obligation_t* add_theorem(formal_theory_t* theory, const char* name, const char* statement);

// Prove all theorems in theory
int prove_theory(formal_theory_t* theory);

// Export theory proofs
bool export_theory_proofs(formal_theory_t* theory, const char* filename);

// Import and verify theory
formal_theory_t* import_verified_theory(const char* filename);

/* ============================================================================
 * Standard library of verified theories
 * ============================================================================ */

// Peano arithmetic
formal_theory_t* create_peano_arithmetic(void);

// Propositional logic
formal_theory_t* create_propositional_logic(void);

// First-order logic
formal_theory_t* create_first_order_logic(void);

// Set theory (ZFC)
formal_theory_t* create_zfc_set_theory(void);

// Group theory
formal_theory_t* create_group_theory(void);

// Field theory
formal_theory_t* create_field_theory(void);

// BaseFold RAA soundness theory
formal_theory_t* create_basefold_soundness_theory(void);

/* ============================================================================
 * Advanced features
 * ============================================================================ */

// Proof composition
proof_obligation_t* compose_proofs(proof_obligation_t* p1, proof_obligation_t* p2);

// Proof by induction
proof_obligation_t* prove_by_induction(
    formal_theory_t* theory,
    const char* base_case,
    const char* inductive_step,
    const char* conclusion
);

// Proof by contradiction
proof_obligation_t* prove_by_contradiction(
    formal_theory_t* theory,
    const char* assumption,
    const char* contradiction
);

// Interactive proof construction
typedef struct proof_assistant proof_assistant_t;
proof_assistant_t* create_proof_assistant(formal_theory_t* theory);
void suggest_next_step(proof_assistant_t* assistant);
void apply_tactic(proof_assistant_t* assistant, const char* tactic);

/* ============================================================================
 * Self-verification
 * ============================================================================ */

// The crown jewel: prove the prover is correct
proof_obligation_t* prove_prover_soundness(void);

// Prove the verifier is correct  
proof_obligation_t* prove_verifier_completeness(void);

// Bootstrap trust
bool bootstrap_formal_system(void);

#endif // FORMAL_PROOF_CIRCUITS_H