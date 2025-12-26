#ifndef CMPTR_EVALUATOR_H
#define CMPTR_EVALUATOR_H

/**
 * @file evaluator.h
 * @brief Real evaluator for gate circuits
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Enumeration of gate types
 */
typedef enum {
    GATE_AND = 0,  /**< Logical AND gate */
    GATE_XOR = 1   /**< Logical XOR gate */
} gate_type_t;

/**
 * @brief Represents a wire in the circuit
 * 
 * Wire IDs are unsigned integers:
 * - 0: Hardcoded constant 0
 * - 1: Hardcoded constant 1
 * - 2 to (num_inputs+1): External inputs
 * - (num_inputs+2) and above: Gate outputs
 */
typedef uint32_t wire_id_t;

/**
 * @brief Structure representing a gate
 */
typedef struct {
    gate_type_t type;    /**< Type of gate (AND or XOR) */
    wire_id_t input1;    /**< First input wire ID */
    wire_id_t input2;    /**< Second input wire ID */
    wire_id_t output;    /**< Output wire ID */
} gate_t;

/**
 * @brief Structure representing a circuit
 */
typedef struct {
    uint32_t num_inputs;         /**< Number of external inputs */
    uint32_t num_gates;          /**< Number of gates in the circuit */
    uint32_t max_gates;          /**< Maximum number of gates allocated */
    uint32_t num_outputs;        /**< Number of circuit outputs */
    gate_t *gates;               /**< Array of gates */
    wire_id_t *output_wires;     /**< Array of output wire IDs */
    uint32_t *layer_offsets;     /**< Offsets for each layer of gates */
    uint32_t num_layers;         /**< Number of layers */
} circuit_t;

/**
 * @brief Structure representing the state of the wires during evaluation
 */
typedef struct {
    uint32_t num_wires;          /**< Total number of wires */
    uint8_t *values;             /**< Binary values for each wire (0 or 1) */
} wire_state_t;

/**
 * @brief Initialize a circuit
 * 
 * @param num_inputs Number of external inputs
 * @param num_gates Number of gates
 * @param num_outputs Number of outputs
 * @return Initialized circuit or NULL on error
 */
circuit_t* evaluator_init_circuit(uint32_t num_inputs, uint32_t num_gates, uint32_t num_outputs);

/**
 * @brief Free a circuit
 * 
 * @param circuit Circuit to free
 */
void evaluator_free_circuit(circuit_t *circuit);

/**
 * @brief Add a gate to the circuit
 * 
 * @param circuit Circuit to add gate to
 * @param type Gate type (AND or XOR)
 * @param input1 First input wire ID
 * @param input2 Second input wire ID
 * @param output Output wire ID
 * @return true if gate was added, false if error
 */
bool evaluator_add_gate(circuit_t *circuit, gate_type_t type, wire_id_t input1, wire_id_t input2, wire_id_t output);

/**
 * @brief Set output wires for the circuit
 * 
 * @param circuit Circuit to set outputs for
 * @param output_wires Array of output wire IDs
 * @param num_outputs Number of outputs
 * @return true if outputs were set, false if error
 */
bool evaluator_set_outputs(circuit_t *circuit, wire_id_t *output_wires, uint32_t num_outputs);

/**
 * @brief Prepare circuit for evaluation by organizing gates into layers
 * 
 * @param circuit Circuit to prepare
 * @return true if preparation successful, false if error
 */
bool evaluator_prepare_circuit(circuit_t *circuit);

/**
 * @brief Initialize wire state for evaluation
 * 
 * @param circuit Circuit to evaluate
 * @return Initialized wire state or NULL on error
 */
wire_state_t* evaluator_init_wire_state(circuit_t *circuit);

/**
 * @brief Free wire state
 * 
 * @param state Wire state to free
 */
void evaluator_free_wire_state(wire_state_t *state);

/**
 * @brief Set input values
 * 
 * @param state Wire state to update
 * @param inputs Array of input values (0 or 1)
 * @param num_inputs Number of inputs
 * @return true if inputs were set, false if error
 */
bool evaluator_set_inputs(wire_state_t *state, const uint8_t *inputs, uint32_t num_inputs);

/**
 * @brief Evaluate circuit with given inputs
 * 
 * @param circuit Circuit to evaluate
 * @param state Wire state with inputs set
 * @return true if evaluation successful, false if error
 */
bool evaluator_evaluate_circuit(circuit_t *circuit, wire_state_t *state);

/**
 * @brief Get output values
 * 
 * @param circuit Circuit that was evaluated
 * @param state Wire state after evaluation
 * @param outputs Array to store output values
 * @return true if outputs were retrieved, false if error
 */
bool evaluator_get_outputs(circuit_t *circuit, wire_state_t *state, uint8_t *outputs);

#ifdef __cplusplus
}
#endif

#endif /* CMPTR_EVALUATOR_H */