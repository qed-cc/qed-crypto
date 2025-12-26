#include "circuit_format.h"
#include <stdlib.h>
#include <string.h>
#include "input_validation.h"

// Buffer for error messages
static char error_buffer[256];

/**
 * @brief Get the last error message
 * 
 * @return Error message string
 */
const char* circuit_format_get_error(void) {
    return error_buffer;
}

/**
 * @brief Load a circuit from a binary file
 * 
 * @param filename Path to the binary circuit file
 * @return Loaded circuit or NULL on error
 */
circuit_t* circuit_load_binary(const char *filename) {
    // Validate file path for security
    validation_result_t path_result = validate_file_path(filename, true, 0);
    if (path_result != VALIDATION_SUCCESS) {
        snprintf(error_buffer, sizeof(error_buffer), 
                 "Invalid file path: %s", validation_error_string(path_result));
        return NULL;
    }
    
    FILE *file = fopen(filename, "rb");
    if (!file) {
        snprintf(error_buffer, sizeof(error_buffer), "Failed to open file: %s", filename);
        return NULL;
    }
    
    // Read the header
    circuit_binary_header_t header;
    if (fread(&header, sizeof(header), 1, file) != 1) {
        snprintf(error_buffer, sizeof(error_buffer), "Failed to read header from file: %s", filename);
        fclose(file);
        return NULL;
    }
    
    // Validate the header
    if (header.magic != CIRCUIT_BINARY_MAGIC) {
        snprintf(error_buffer, sizeof(error_buffer), "Invalid magic number in file: %s", filename);
        fclose(file);
        return NULL;
    }
    
    if (header.version != CIRCUIT_BINARY_VERSION) {
        snprintf(error_buffer, sizeof(error_buffer), "Unsupported version %u in file: %s", 
                 header.version, filename);
        fclose(file);
        return NULL;
    }
    
    // SECURITY FIX: Validate header values against reasonable limits
    const uint32_t MAX_GATES = (1U << 24);      // 16 million gates max
    const uint32_t MAX_INPUTS = (1U << 20);     // 1 million inputs max
    const uint32_t MAX_OUTPUTS = (1U << 20);    // 1 million outputs max
    const uint32_t MAX_LAYERS = (1U << 16);     // 65K layers max
    
    if (header.num_gates > MAX_GATES) {
        snprintf(error_buffer, sizeof(error_buffer), "Unreasonable number of gates: %u", header.num_gates);
        fclose(file);
        return NULL;
    }
    
    if (header.num_inputs > MAX_INPUTS) {
        snprintf(error_buffer, sizeof(error_buffer), "Unreasonable number of inputs: %u", header.num_inputs);
        fclose(file);
        return NULL;
    }
    
    if (header.num_outputs > MAX_OUTPUTS) {
        snprintf(error_buffer, sizeof(error_buffer), "Unreasonable number of outputs: %u", header.num_outputs);
        fclose(file);
        return NULL;
    }
    
    if (header.num_layers > MAX_LAYERS) {
        snprintf(error_buffer, sizeof(error_buffer), "Unreasonable number of layers: %u", header.num_layers);
        fclose(file);
        return NULL;
    }
    
    // Create the circuit
    circuit_t *circuit = evaluator_init_circuit(header.num_inputs, header.num_gates, header.num_outputs);
    if (!circuit) {
        snprintf(error_buffer, sizeof(error_buffer), "Failed to initialize circuit");
        fclose(file);
        return NULL;
    }
    
    // Read the gates
    if (header.num_gates > 0) {
        // Seek to the gates section
        if (fseek(file, header.gates_offset, SEEK_SET) != 0) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to seek to gates section");
            evaluator_free_circuit(circuit);
            fclose(file);
            return NULL;
        }
        
        // Allocate a buffer for the binary gates
        // SECURITY FIX: Check for integer overflow before allocation
        size_t gates_size;
        if (header.num_gates > SIZE_MAX / sizeof(circuit_binary_gate_t)) {
            snprintf(error_buffer, sizeof(error_buffer), "Integer overflow in gates allocation");
            evaluator_free_circuit(circuit);
            fclose(file);
            return NULL;
        }
        gates_size = header.num_gates * sizeof(circuit_binary_gate_t);
        
        circuit_binary_gate_t *binary_gates = malloc(gates_size);
        if (!binary_gates) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to allocate memory for gates");
            evaluator_free_circuit(circuit);
            fclose(file);
            return NULL;
        }
        
        // Read the binary gates
        if (fread(binary_gates, sizeof(circuit_binary_gate_t), header.num_gates, file) != header.num_gates) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to read gates from file");
            free(binary_gates);
            evaluator_free_circuit(circuit);
            fclose(file);
            return NULL;
        }
        
        // Convert binary gates to circuit gates
        for (uint32_t i = 0; i < header.num_gates; i++) {
            gate_type_t type = (gate_type_t)binary_gates[i].type;
            if (!evaluator_add_gate(circuit, type, binary_gates[i].input1, 
                                   binary_gates[i].input2, binary_gates[i].output)) {
                snprintf(error_buffer, sizeof(error_buffer), "Failed to add gate %u", i);
                free(binary_gates);
                evaluator_free_circuit(circuit);
                fclose(file);
                return NULL;
            }
        }
        
        free(binary_gates);
    }
    
    // Read the output wires
    if (header.num_outputs > 0) {
        // Seek to the outputs section
        if (fseek(file, header.outputs_offset, SEEK_SET) != 0) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to seek to outputs section");
            evaluator_free_circuit(circuit);
            fclose(file);
            return NULL;
        }
        
        // Allocate a buffer for the output wires
        wire_id_t *output_wires = safe_calloc(header.num_outputs, sizeof(wire_id_t));
        if (!output_wires) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to allocate memory for output wires");
            evaluator_free_circuit(circuit);
            fclose(file);
            return NULL;
        }
        
        // Read the output wires
        if (fread(output_wires, sizeof(wire_id_t), header.num_outputs, file) != header.num_outputs) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to read output wires from file");
            free(output_wires);
            evaluator_free_circuit(circuit);
            fclose(file);
            return NULL;
        }
        
        // Validate output wire IDs
        for (uint32_t i = 0; i < header.num_outputs; i++) {
            if (!validate_wire_id(output_wires[i], MAX_WIRE_ID)) {
                snprintf(error_buffer, sizeof(error_buffer), "Output wire ID %u exceeds maximum", output_wires[i]);
                free(output_wires);
                evaluator_free_circuit(circuit);
                fclose(file);
                return NULL;
            }
        }
        
        // Set the output wires
        if (!evaluator_set_outputs(circuit, output_wires, header.num_outputs)) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to set circuit outputs");
            free(output_wires);
            evaluator_free_circuit(circuit);
            fclose(file);
            return NULL;
        }
        
        free(output_wires);
    }
    
    // Read the layer offsets if present
    if (header.num_layers > 0 && header.layers_offset > 0) {
        // Seek to the layers section
        if (fseek(file, header.layers_offset, SEEK_SET) != 0) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to seek to layers section");
            evaluator_free_circuit(circuit);
            fclose(file);
            return NULL;
        }
        
        // Allocate memory for the layer offsets
        // SECURITY FIX: Check for integer overflow
        size_t layer_offsets_count = (size_t)header.num_layers + 1;
        if (layer_offsets_count == 0 || layer_offsets_count > SIZE_MAX / sizeof(uint32_t)) {
            snprintf(error_buffer, sizeof(error_buffer), "Integer overflow in layer offsets allocation");
            evaluator_free_circuit(circuit);
            fclose(file);
            return NULL;
        }
        
        circuit->layer_offsets = malloc(layer_offsets_count * sizeof(uint32_t));
        if (!circuit->layer_offsets) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to allocate memory for layer offsets");
            evaluator_free_circuit(circuit);
            fclose(file);
            return NULL;
        }
        
        // Read the layer offsets
        if (fread(circuit->layer_offsets, sizeof(uint32_t), header.num_layers + 1, file) != header.num_layers + 1) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to read layer offsets from file");
            evaluator_free_circuit(circuit);
            fclose(file);
            return NULL;
        }
        
        circuit->num_layers = header.num_layers;
    } else {
        // Prepare the circuit (organize gates into layers)
        if (!evaluator_prepare_circuit(circuit)) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to prepare circuit");
            evaluator_free_circuit(circuit);
            fclose(file);
            return NULL;
        }
    }
    
    fclose(file);
    return circuit;
}

/**
 * @brief Save a circuit to a binary file
 * 
 * @param circuit Circuit to save
 * @param filename Path to the output file
 * @return true if successful, false if error
 */
bool circuit_save_binary(circuit_t *circuit, const char *filename) {
    if (!circuit) {
        snprintf(error_buffer, sizeof(error_buffer), "Invalid circuit (NULL)");
        return false;
    }
    
    // Validate file path for security
    validation_result_t path_result = validate_file_path(filename, true, 0);
    if (path_result != VALIDATION_SUCCESS) {
        snprintf(error_buffer, sizeof(error_buffer), 
                 "Invalid file path: %s", validation_error_string(path_result));
        return false;
    }
    
    FILE *file = fopen(filename, "wb");
    if (!file) {
        snprintf(error_buffer, sizeof(error_buffer), "Failed to open file for writing: %s", filename);
        return false;
    }
    
    // If the circuit is not prepared, prepare it first
    if (circuit->num_layers == 0 || !circuit->layer_offsets) {
        if (!evaluator_prepare_circuit(circuit)) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to prepare circuit for saving");
            fclose(file);
            return false;
        }
    }
    
    // Initialize the header
    circuit_binary_header_t header;
    memset(&header, 0, sizeof(header));
    
    header.magic = CIRCUIT_BINARY_MAGIC;
    header.version = CIRCUIT_BINARY_VERSION;
    header.header_size = sizeof(header);
    header.num_inputs = circuit->num_inputs;
    header.num_gates = circuit->num_gates;
    header.num_outputs = circuit->num_outputs;
    header.num_layers = circuit->num_layers;
    
    // Calculate offsets
    header.gates_offset = sizeof(header);
    header.outputs_offset = header.gates_offset + circuit->num_gates * sizeof(circuit_binary_gate_t);
    header.layers_offset = header.outputs_offset + circuit->num_outputs * sizeof(wire_id_t);
    header.circuit_size = header.layers_offset + (circuit->num_layers + 1) * sizeof(uint32_t);
    
    // Write the header
    if (fwrite(&header, sizeof(header), 1, file) != 1) {
        snprintf(error_buffer, sizeof(error_buffer), "Failed to write header to file");
        fclose(file);
        return false;
    }
    
    // Write the gates
    if (circuit->num_gates > 0) {
        // Allocate a buffer for the binary gates
        circuit_binary_gate_t *binary_gates = malloc(circuit->num_gates * sizeof(circuit_binary_gate_t));
        if (!binary_gates) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to allocate memory for binary gates");
            fclose(file);
            return false;
        }
        
        // Convert circuit gates to binary format
        for (uint32_t i = 0; i < circuit->num_gates; i++) {
            memset(&binary_gates[i], 0, sizeof(circuit_binary_gate_t));
            binary_gates[i].type = (uint8_t)circuit->gates[i].type;
            binary_gates[i].input1 = circuit->gates[i].input1;
            binary_gates[i].input2 = circuit->gates[i].input2;
            binary_gates[i].output = circuit->gates[i].output;
        }
        
        // Write the binary gates
        if (fwrite(binary_gates, sizeof(circuit_binary_gate_t), circuit->num_gates, file) != circuit->num_gates) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to write gates to file");
            free(binary_gates);
            fclose(file);
            return false;
        }
        
        free(binary_gates);
    }
    
    // Write the output wires
    if (circuit->num_outputs > 0) {
        if (fwrite(circuit->output_wires, sizeof(wire_id_t), circuit->num_outputs, file) != circuit->num_outputs) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to write output wires to file");
            fclose(file);
            return false;
        }
    }
    
    // Write the layer offsets
    if (circuit->num_layers > 0 && circuit->layer_offsets) {
        if (fwrite(circuit->layer_offsets, sizeof(uint32_t), circuit->num_layers + 1, file) != circuit->num_layers + 1) {
            snprintf(error_buffer, sizeof(error_buffer), "Failed to write layer offsets to file");
            fclose(file);
            return false;
        }
    }
    
    fclose(file);
    return true;
}