#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include "evaluator.h"
#include "input_validation.h"
#include "logger.h"

/* Include basefold trace conditionally */
#ifdef ENABLE_BASEFOLD_TRACE
#include "basefold_trace.h"
#endif

/**
 * @brief Initialize a circuit
 * 
 * @param num_inputs Number of external inputs
 * @param num_gates Number of gates
 * @param num_outputs Number of outputs
 * @return Initialized circuit or NULL on error
 */
circuit_t* evaluator_init_circuit(uint32_t num_inputs, uint32_t num_gates, uint32_t num_outputs) {
    // Validate circuit parameters first
    if (validate_circuit_params(num_inputs, num_outputs, num_gates) != VALIDATION_SUCCESS) {
        LOG_ERROR("evaluator", "Invalid circuit parameters: inputs=%u, outputs=%u, gates=%u",
                num_inputs, num_outputs, num_gates);
        return NULL;
    }
    
    circuit_t* circuit = calloc(1, sizeof(circuit_t));
    if (!circuit) {
        return NULL;
    }
    
    circuit->num_inputs = num_inputs;
    circuit->num_gates = 0;
    circuit->max_gates = num_gates;
    circuit->num_outputs = num_outputs;
    
    // Use safe allocation with overflow checking
    circuit->gates = safe_calloc(num_gates, sizeof(gate_t));
    circuit->output_wires = safe_calloc(num_outputs, sizeof(wire_id_t));
    circuit->layer_offsets = NULL;
    circuit->num_layers = 0;
    
    if (!circuit->gates || !circuit->output_wires) {
        evaluator_free_circuit(circuit);
        return NULL;
    }
    
    return circuit;
}

/**
 * @brief Free a circuit
 * 
 * @param circuit Circuit to free
 */
void evaluator_free_circuit(circuit_t *circuit) {
    if (circuit) {
        free(circuit->gates);
        free(circuit->output_wires);
        free(circuit->layer_offsets);
        free(circuit);
    }
}

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
bool evaluator_add_gate(circuit_t *circuit, gate_type_t type, wire_id_t input1, wire_id_t input2, wire_id_t output) {
    if (!circuit || !circuit->gates) {
        return false;
    }
    
    // Validate gate type
    if (type != GATE_AND && type != GATE_XOR) {
        LOG_ERROR("evaluator", "Invalid gate type: %d", type);
        return false;
    }
    
    // Validate wire IDs
    if (!validate_wire_id(input1, MAX_WIRE_ID) || !validate_wire_id(input2, MAX_WIRE_ID) ||
        !validate_wire_id(output, MAX_WIRE_ID)) {
        LOG_ERROR("evaluator", "Wire ID exceeds maximum allowed value");
        return false;
    }
    
    // Dynamically resize the gates array if needed
    if (circuit->num_gates >= circuit->max_gates) {
        // Check for overflow in new capacity
        if (circuit->max_gates > MAX_CIRCUIT_GATES / 2) {
            LOG_ERROR("evaluator", "Cannot resize gates array: would exceed maximum");
            return false;
        }
        
        uint32_t new_capacity = circuit->max_gates * 2;
        gate_t *new_gates = safe_realloc(circuit->gates, new_capacity, sizeof(gate_t));
        if (!new_gates) {
            LOG_ERROR("evaluator", "Failed to resize gates array");
            return false;
        }
        circuit->gates = new_gates;
        circuit->max_gates = new_capacity;
    }
    
    gate_t *gate = &circuit->gates[circuit->num_gates];
    gate->type = type;
    gate->input1 = input1;
    gate->input2 = input2;
    gate->output = output;
    circuit->num_gates++;
    
    return true;
}

/**
 * @brief Set output wires for the circuit
 * 
 * @param circuit Circuit to set outputs for
 * @param output_wires Array of output wire IDs
 * @param num_outputs Number of outputs
 * @return true if outputs were set, false if error
 */
bool evaluator_set_outputs(circuit_t *circuit, wire_id_t *output_wires, uint32_t num_outputs) {
    if (!circuit || !circuit->output_wires || !output_wires || num_outputs != circuit->num_outputs) {
        return false;
    }
    
    memcpy(circuit->output_wires, output_wires, num_outputs * sizeof(wire_id_t));
    return true;
}

/**
 * @brief Find dependencies between gates and organize them into layers
 * 
 * A layer contains gates whose inputs only depend on constants, inputs, or gates in previous layers
 * 
 * @param circuit Circuit to organize
 * @return true if organization successful, false if error
 */
bool evaluate_dependencies(circuit_t *circuit) {
    if (!circuit || circuit->num_gates == 0) {
        return true; // Empty circuit is already layered
    }
    
    // First, determine the maximum wire ID used in the circuit
    wire_id_t max_wire_id = 0;
    
    // Check gates for max wire ID
    for (uint32_t i = 0; i < circuit->num_gates; i++) {
        gate_t *gate = &circuit->gates[i];
        if (gate->input1 > max_wire_id) max_wire_id = gate->input1;
        if (gate->input2 > max_wire_id) max_wire_id = gate->input2;
        if (gate->output > max_wire_id) max_wire_id = gate->output;
    }
    
    // Check outputs for max wire ID
    for (uint32_t i = 0; i < circuit->num_outputs; i++) {
        if (circuit->output_wires[i] > max_wire_id) {
            max_wire_id = circuit->output_wires[i];
        }
    }
    
    // Validate max wire ID
    if (max_wire_id > MAX_WIRE_ID) {
        LOG_ERROR("evaluator", "Wire ID %u exceeds maximum allowed %u", max_wire_id, MAX_WIRE_ID);
        return false;
    }
    
    // Allocate array to track when each wire is computed
    uint32_t *wire_layer = safe_calloc(max_wire_id + 1, sizeof(uint32_t));
    if (!wire_layer) {
        return false;
    }
    
    // Constant wires (0 and 1) and input wires (2 to num_inputs+1) are available at layer 0
    for (wire_id_t i = 0; i <= circuit->num_inputs + 1; i++) {
        wire_layer[i] = 0;
    }
    
    // Organize gates into layers
    bool changed;
    uint32_t max_layer = 0;
    
    do {
        changed = false;
        
        for (uint32_t i = 0; i < circuit->num_gates; i++) {
            gate_t *gate = &circuit->gates[i];
            
            // If this gate has not been assigned to a layer yet (output wire is 0)
            if (wire_layer[gate->output] == 0) {
                // Check if both inputs are available
                if (wire_layer[gate->input1] > 0 || gate->input1 <= circuit->num_inputs + 1) {
                    if (wire_layer[gate->input2] > 0 || gate->input2 <= circuit->num_inputs + 1) {
                        // Inputs are available, assign this gate to the next layer
                        uint32_t layer = 1;
                        if (gate->input1 > circuit->num_inputs + 1) {
                            layer = wire_layer[gate->input1] + 1;
                        }
                        if (gate->input2 > circuit->num_inputs + 1 && wire_layer[gate->input2] + 1 > layer) {
                            layer = wire_layer[gate->input2] + 1;
                        }
                        
                        wire_layer[gate->output] = layer;
                        if (layer > max_layer) {
                            max_layer = layer;
                        }
                        
                        changed = true;
                    }
                }
            }
        }
    } while (changed);
    
    // SECURITY FIX: Enhanced cycle detection with specific error reporting
    bool has_cycles = false;
    for (uint32_t i = 0; i < circuit->num_gates; i++) {
        gate_t *gate = &circuit->gates[i];
        if (wire_layer[gate->output] == 0) {
            // Detailed cycle analysis
            if (gate->input1 == gate->output || gate->input2 == gate->output) {
                LOG_ERROR("evaluator", "Gate %u has self-referential connection (output %u feeds back to input)", 
                        i, gate->output);
            } else {
                LOG_ERROR("evaluator", "Gate %u (inputs %u,%u -> output %u) is part of a dependency cycle", 
                        i, gate->input1, gate->input2, gate->output);
            }
            has_cycles = true;
        }
    }
    
    if (has_cycles) {
        LOG_ERROR("evaluator", "Circuit has cyclic dependencies - cannot be evaluated safely");
        free(wire_layer);
        return false;
    }
    
    // SECURITY FIX: Circuit complexity validation to prevent resource exhaustion
    if (max_layer > 10000) {  // Reasonable depth limit
        LOG_ERROR("evaluator", "Circuit depth %u exceeds maximum allowed (10000 layers)", max_layer);
        LOG_ERROR("evaluator", "This may indicate a very deep circuit or inefficient layering");
        free(wire_layer);
        return false;
    }
    
    // Calculate estimated memory usage
    size_t estimated_memory = (size_t)circuit->num_gates * sizeof(gate_t) + 
                             (size_t)(max_wire_id + 1) * sizeof(uint8_t) +
                             (size_t)(max_layer + 1) * sizeof(uint32_t);
    
    if (estimated_memory > 1024 * 1024 * 1024) {  // 1GB limit
        LOG_ERROR("evaluator", "Circuit requires approximately %zu MB of memory", 
                estimated_memory / (1024 * 1024));
        LOG_ERROR("evaluator", "This exceeds the 1GB safety limit for circuit evaluation");
        free(wire_layer);
        return false;
    }
    
    // Count gates in each layer
    uint32_t *layer_sizes = safe_calloc(max_layer + 1, sizeof(uint32_t));
    if (!layer_sizes) {
        free(wire_layer);
        return false;
    }
    
    for (uint32_t i = 0; i < circuit->num_gates; i++) {
        gate_t *gate = &circuit->gates[i];
        layer_sizes[wire_layer[gate->output]]++;
    }
    
    // Allocate array for layer offsets
    circuit->num_layers = max_layer;
    circuit->layer_offsets = safe_calloc(max_layer + 1, sizeof(uint32_t));
    if (!circuit->layer_offsets) {
        free(wire_layer);
        free(layer_sizes);
        return false;
    }
    
    // Calculate cumulative offsets for each layer
    circuit->layer_offsets[0] = 0;
    for (uint32_t i = 1; i <= max_layer; i++) {
        circuit->layer_offsets[i] = circuit->layer_offsets[i-1] + layer_sizes[i];
    }
    
    // Sort gates into layers
    gate_t *sorted_gates = safe_calloc(circuit->num_gates, sizeof(gate_t));
    if (!sorted_gates) {
        free(wire_layer);
        free(layer_sizes);
        return false;
    }
    
    // Initialize counters for each layer
    uint32_t *layer_counters = safe_calloc(max_layer + 1, sizeof(uint32_t));
    if (!layer_counters) {
        free(wire_layer);
        free(layer_sizes);
        free(sorted_gates);
        return false;
    }
    
    // Place gates in sorted order
    for (uint32_t i = 0; i < circuit->num_gates; i++) {
        gate_t *gate = &circuit->gates[i];
        uint32_t layer = wire_layer[gate->output];
        uint32_t index = circuit->layer_offsets[layer-1] + layer_counters[layer]++;
        memcpy(&sorted_gates[index], gate, sizeof(gate_t));
    }
    
    // Replace the original gates with sorted gates
    free(circuit->gates);
    circuit->gates = sorted_gates;
    
    // Clean up
    free(wire_layer);
    free(layer_sizes);
    free(layer_counters);
    
    return true;
}

/**
 * @brief Prepare circuit for evaluation by organizing gates into layers
 * 
 * @param circuit Circuit to prepare
 * @return true if preparation successful, false if error
 */
bool evaluator_prepare_circuit(circuit_t *circuit) {
    if (!circuit) {
        return false;
    }
    
    // Free old layer_offsets if it exists
    if (circuit->layer_offsets) {
        free(circuit->layer_offsets);
        circuit->layer_offsets = NULL;
        circuit->num_layers = 0;
    }
    
    return evaluate_dependencies(circuit);
}

/**
 * @brief Initialize wire state for evaluation
 * 
 * @param circuit Circuit to evaluate
 * @return Initialized wire state or NULL on error
 */
wire_state_t* evaluator_init_wire_state(circuit_t *circuit) {
    if (!circuit) {
        return NULL;
    }
    
    // Find the highest wire ID used in the circuit
    wire_id_t max_wire_id = 0;
    
    // Check gates for max wire ID
    for (uint32_t i = 0; i < circuit->num_gates; i++) {
        gate_t *gate = &circuit->gates[i];
        if (gate->input1 > max_wire_id) max_wire_id = gate->input1;
        if (gate->input2 > max_wire_id) max_wire_id = gate->input2;
        if (gate->output > max_wire_id) max_wire_id = gate->output;
    }
    
    // Check outputs for max wire ID
    for (uint32_t i = 0; i < circuit->num_outputs; i++) {
        if (circuit->output_wires[i] > max_wire_id) {
            max_wire_id = circuit->output_wires[i];
        }
    }
    
    wire_state_t *state = malloc(sizeof(wire_state_t));
    if (!state) {
        return NULL;
    }
    
    state->num_wires = max_wire_id + 1;
    // SECURITY FIX: Use safe_calloc to prevent integer overflow in allocation
    state->values = safe_calloc(state->num_wires, sizeof(uint8_t));
    
    if (!state->values) {
        LOG_ERROR("evaluator", "Failed to allocate memory for %u wire states", state->num_wires);
        free(state);
        return NULL;
    }
    
    // Initialize constants
    state->values[0] = 0; // Constant 0
    state->values[1] = 1; // Constant 1
    
    return state;
}

/**
 * @brief Free wire state
 * 
 * @param state Wire state to free
 */
void evaluator_free_wire_state(wire_state_t *state) {
    if (state) {
        free(state->values);
        free(state);
    }
}

/**
 * @brief Set input values for the circuit
 * 
 * @param state Wire state to update
 * @param inputs Array of input values (0 or 1)
 * @param num_inputs Number of inputs
 * @return true if inputs were set, false if error
 */
bool evaluator_set_inputs(wire_state_t *state, const uint8_t *inputs, uint32_t num_inputs) {
    if (!state || !state->values || !inputs) {
        return false;
    }
    
    // Validate num_inputs
    if (num_inputs > MAX_CIRCUIT_INPUTS) {
        LOG_ERROR("evaluator", "Number of inputs %u exceeds maximum %u", num_inputs, MAX_CIRCUIT_INPUTS);
        return false;
    }
    
    // Check if we have enough wires for all inputs
    if (num_inputs + 2 > state->num_wires) {
        LOG_ERROR("evaluator", "Not enough wires for %u inputs (need %u, have %u)", 
                num_inputs, num_inputs + 2, state->num_wires);
        return false;
    }
    
    // Copy inputs to the appropriate wire IDs (starting from 2)
    for (uint32_t i = 0; i < num_inputs; i++) {
        state->values[i + 2] = inputs[i] ? 1 : 0; // Ensure binary values
    }
    
    return true;
}

/**
 * @brief Evaluate the circuit with the given inputs
 * 
 * @param circuit Circuit to evaluate
 * @param state Wire state with inputs set
 * @return true if evaluation successful, false if error
 */
bool evaluator_evaluate_circuit(circuit_t *circuit, wire_state_t *state) {
    if (!circuit || !state || !state->values || !circuit->gates) {
        return false;
    }
    
    // Evaluate gates layer by layer
    for (uint32_t layer = 0; layer < circuit->num_layers; layer++) {
        uint32_t start = circuit->layer_offsets[layer];
        uint32_t end = circuit->layer_offsets[layer + 1];
        
        // Evaluate all gates in this layer
        for (uint32_t i = start; i < end; i++) {
            gate_t *gate = &circuit->gates[i];
            
            // Validate wire IDs are within bounds
            if (gate->input1 >= state->num_wires || gate->input2 >= state->num_wires ||
                gate->output >= state->num_wires) {
                LOG_ERROR("evaluator", "Gate wire ID out of bounds at gate %u", i);
                return false;
            }
            
            // Get input values
            uint8_t input1_val = state->values[gate->input1];
            uint8_t input2_val = state->values[gate->input2];
            
            // Compute output value based on gate type
            uint8_t output_val = 0;
            
            if (gate->type == GATE_AND) {
                output_val = input1_val & input2_val;
            } else if (gate->type == GATE_XOR) {
                output_val = input1_val ^ input2_val;
            } else {
                LOG_ERROR("evaluator", "Invalid gate type %d at gate %u", gate->type, i);
                return false;
            }
            
            // Set output value
            state->values[gate->output] = output_val;
        }
    }
    
    return true;
}

/**
 * @brief Get output values from the evaluated circuit
 * 
 * @param circuit Circuit that was evaluated
 * @param state Wire state after evaluation
 * @param outputs Array to store output values
 * @return true if outputs were retrieved, false if error
 */
bool evaluator_get_outputs(circuit_t *circuit, wire_state_t *state, uint8_t *outputs) {
    if (!circuit || !state || !state->values || !outputs || !circuit->output_wires) {
        return false;
    }
    
    // Copy output values from the corresponding wire IDs
    for (uint32_t i = 0; i < circuit->num_outputs; i++) {
        wire_id_t wire_id = circuit->output_wires[i];
        
        if (wire_id >= state->num_wires) {
            LOG_ERROR("evaluator", "Output wire ID %u is out of range", wire_id);
            return false;
        }
        
        outputs[i] = state->values[wire_id];
    }
    
    return true;
}

/**
 * @brief Evaluate circuit with trace recording
 */
bool evaluator_evaluate_circuit_with_trace(circuit_t *circuit, wire_state_t *state, basefold_trace_t *trace) {
    if (!circuit || !state || !state->values || !circuit->gates) {
        return false;
    }
    
    // Evaluate gates layer by layer
    for (uint32_t layer = 0; layer < circuit->num_layers; layer++) {
        uint32_t start = circuit->layer_offsets[layer];
        uint32_t end = circuit->layer_offsets[layer + 1];
        
        // Evaluate all gates in this layer
        for (uint32_t i = start; i < end; i++) {
            gate_t *gate = &circuit->gates[i];
            
            // Get input values
            uint8_t input1_val = state->values[gate->input1];
            uint8_t input2_val = state->values[gate->input2];
            
            // Compute output value based on gate type
            uint8_t output_val = 0;
            
            if (gate->type == GATE_AND) {
                output_val = input1_val & input2_val;
            } else if (gate->type == GATE_XOR) {
                output_val = input1_val ^ input2_val;
            }
            
            // Set output value
            state->values[gate->output] = output_val;
            
            // Record trace if provided
#ifdef ENABLE_BASEFOLD_TRACE
            if (trace) {
                uint8_t gate_type_bit = (gate->type == GATE_AND) ? 1 : 0;
                if (!basefold_trace_record_gate(trace, input1_val, input2_val, output_val, gate_type_bit)) {
                    LOG_ERROR("evaluator", "Failed to record gate trace at gate %u", i);
                    return false;
                }
            }
#endif
        }
    }
    
    return true;
}