/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_vrf.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

void print_hex(const char* label, const uint8_t* data, size_t len) {
    printf("%s: ", label);
    for (size_t i = 0; i < len && i < 32; i++) {
        printf("%02x", data[i]);
    }
    if (len > 32) printf("... (%zu bytes total)", len);
    printf("\n");
}

void demo_basic_vrf() {
    printf("=== Basic VRF Demo ===\n\n");
    
    // Initialize VRF system
    cmptr_vrf_system_t* system = cmptr_vrf_init();
    
    // Generate VRF key pair
    cmptr_vrf_secret_t* secret_key;
    cmptr_vrf_public_t* public_key;
    
    clock_t start = clock();
    cmptr_vrf_keygen(system, &secret_key, &public_key);
    clock_t end = clock();
    double keygen_ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000;
    
    printf("Key generation: %.2f ms\n", keygen_ms);
    
    // Export and show public key
    uint8_t public_bytes[CMPTR_VRF_PUBLIC_SIZE];
    cmptr_vrf_public_export(public_key, public_bytes);
    print_hex("Public key", public_bytes, CMPTR_VRF_PUBLIC_SIZE);
    
    // Evaluate VRF on different inputs
    const char* inputs[] = {
        "block_1000",
        "block_1001", 
        "block_1002",
        "alice@example.com",
        "consensus_round_42"
    };
    
    printf("\n=== VRF Evaluations ===\n");
    
    for (size_t i = 0; i < sizeof(inputs) / sizeof(inputs[0]); i++) {
        const char* input = inputs[i];
        
        // Evaluate VRF
        start = clock();
        cmptr_vrf_result_t* result = cmptr_vrf_eval(
            system, secret_key, 
            (const uint8_t*)input, strlen(input)
        );
        end = clock();
        double eval_ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000;
        
        // Get output
        uint8_t output[CMPTR_VRF_OUTPUT_SIZE];
        cmptr_vrf_result_output(result, output);
        
        printf("\nInput: \"%s\"\n", input);
        print_hex("Output", output, CMPTR_VRF_OUTPUT_SIZE);
        printf("Evaluation time: %.2f ms\n", eval_ms);
        
        // Verify proof
        start = clock();
        bool valid = cmptr_vrf_verify(
            system, public_key,
            (const uint8_t*)input, strlen(input),
            output, result->proof
        );
        end = clock();
        double verify_ms = ((double)(end - start) / CLOCKS_PER_SEC) * 1000;
        
        printf("Verification: %s (%.2f ms)\n", 
               valid ? "✓ Valid" : "✗ Invalid", verify_ms);
        
        cmptr_vrf_result_free(result);
    }
    
    // Demonstrate determinism
    printf("\n=== Determinism Test ===\n");
    const char* test_input = "determinism_test";
    
    cmptr_vrf_result_t* result1 = cmptr_vrf_eval(
        system, secret_key,
        (const uint8_t*)test_input, strlen(test_input)
    );
    
    cmptr_vrf_result_t* result2 = cmptr_vrf_eval(
        system, secret_key,
        (const uint8_t*)test_input, strlen(test_input)
    );
    
    uint8_t output1[CMPTR_VRF_OUTPUT_SIZE];
    uint8_t output2[CMPTR_VRF_OUTPUT_SIZE];
    
    cmptr_vrf_result_output(result1, output1);
    cmptr_vrf_result_output(result2, output2);
    
    bool deterministic = memcmp(output1, output2, CMPTR_VRF_OUTPUT_SIZE) == 0;
    printf("Same input produces same output: %s\n", 
           deterministic ? "✓ Yes (deterministic)" : "✗ No (ERROR!)");
    
    print_hex("Output 1", output1, CMPTR_VRF_OUTPUT_SIZE);
    print_hex("Output 2", output2, CMPTR_VRF_OUTPUT_SIZE);
    
    cmptr_vrf_result_free(result1);
    cmptr_vrf_result_free(result2);
    
    // Cleanup
    cmptr_vrf_secret_free(secret_key);
    cmptr_vrf_public_free(public_key);
    cmptr_vrf_system_free(system);
}

void demo_committee_selection() {
    printf("\n\n=== Committee Selection Demo ===\n");
    printf("Using VRF for fair validator selection\n\n");
    
    cmptr_vrf_system_t* system = cmptr_vrf_init();
    cmptr_vrf_domain_separate(system, "consensus_v1");
    
    // Simulate validators with different stakes
    typedef struct {
        char name[32];
        cmptr_vrf_secret_t* secret;
        cmptr_vrf_public_t* public;
        uint64_t stake;
    } validator_t;
    
    validator_t validators[5] = {
        {.name = "Alice", .stake = 1000000},
        {.name = "Bob",   .stake = 500000},
        {.name = "Carol", .stake = 2000000},
        {.name = "Dave",  .stake = 750000},
        {.name = "Eve",   .stake = 1500000}
    };
    
    // Generate keys for each validator
    for (int i = 0; i < 5; i++) {
        cmptr_vrf_keygen(system, &validators[i].secret, &validators[i].public);
    }
    
    // Simulate committee selection for different rounds
    for (int round = 100; round < 105; round++) {
        printf("\n=== Round %d Committee ===\n", round);
        
        char round_input[64];
        snprintf(round_input, sizeof(round_input), "round_%d", round);
        
        typedef struct {
            int validator_idx;
            uint8_t vrf_output[CMPTR_VRF_OUTPUT_SIZE];
            uint64_t weighted_output;
        } candidate_t;
        
        candidate_t candidates[5];
        
        // Each validator computes VRF
        for (int i = 0; i < 5; i++) {
            cmptr_vrf_result_t* result = cmptr_vrf_eval(
                system, validators[i].secret,
                (const uint8_t*)round_input, strlen(round_input)
            );
            
            candidates[i].validator_idx = i;
            cmptr_vrf_result_output(result, candidates[i].vrf_output);
            
            // Weight by stake (simplified: just use first 8 bytes as uint64)
            uint64_t vrf_value;
            memcpy(&vrf_value, candidates[i].vrf_output, 8);
            candidates[i].weighted_output = vrf_value / (UINT64_MAX / validators[i].stake);
            
            cmptr_vrf_result_free(result);
        }
        
        // Sort by weighted output (simple bubble sort)
        for (int i = 0; i < 4; i++) {
            for (int j = 0; j < 4 - i; j++) {
                if (candidates[j].weighted_output < candidates[j+1].weighted_output) {
                    candidate_t temp = candidates[j];
                    candidates[j] = candidates[j+1];
                    candidates[j+1] = temp;
                }
            }
        }
        
        // Select top 3 for committee
        printf("Committee members:\n");
        for (int i = 0; i < 3; i++) {
            int idx = candidates[i].validator_idx;
            printf("  %d. %s (stake: %lu)\n", 
                   i+1, validators[idx].name, validators[idx].stake);
            print_hex("     VRF", candidates[i].vrf_output, 16);
        }
    }
    
    // Cleanup
    for (int i = 0; i < 5; i++) {
        cmptr_vrf_secret_free(validators[i].secret);
        cmptr_vrf_public_free(validators[i].public);
    }
    cmptr_vrf_system_free(system);
}

void demo_lottery_fairness() {
    printf("\n\n=== Lottery Fairness Demo ===\n");
    printf("Provably fair lottery using VRF\n\n");
    
    cmptr_vrf_system_t* system = cmptr_vrf_init();
    cmptr_vrf_domain_separate(system, "lottery_v1");
    
    // Lottery operator generates keys
    cmptr_vrf_secret_t* operator_secret;
    cmptr_vrf_public_t* operator_public;
    cmptr_vrf_keygen(system, &operator_secret, &operator_public);
    
    // Publish public key
    uint8_t public_bytes[CMPTR_VRF_PUBLIC_SIZE];
    cmptr_vrf_public_export(operator_public, public_bytes);
    printf("Lottery operator public key (published before entries close):\n");
    print_hex("Public key", public_bytes, CMPTR_VRF_PUBLIC_SIZE);
    
    // Simulate lottery entries
    const char* entries[] = {
        "ticket_000001",
        "ticket_000002", 
        "ticket_000003",
        "ticket_000004",
        "ticket_000005"
    };
    
    // After entries close, compute winning number
    const char* lottery_seed = "lottery_2025_01_15_daily";
    
    cmptr_vrf_result_t* result = cmptr_vrf_eval(
        system, operator_secret,
        (const uint8_t*)lottery_seed, strlen(lottery_seed)
    );
    
    uint8_t vrf_output[CMPTR_VRF_OUTPUT_SIZE];
    cmptr_vrf_result_output(result, vrf_output);
    
    // Use VRF output to select winner
    uint32_t winning_index;
    memcpy(&winning_index, vrf_output, 4);
    winning_index = winning_index % 5;  // 5 tickets
    
    printf("\n=== Lottery Results ===\n");
    printf("Seed: \"%s\"\n", lottery_seed);
    print_hex("VRF output", vrf_output, CMPTR_VRF_OUTPUT_SIZE);
    printf("Winning ticket: %s (index %u)\n", entries[winning_index], winning_index);
    
    // Anyone can verify
    printf("\n=== Public Verification ===\n");
    
    // Export proof
    uint8_t proof_data[4096];
    size_t proof_len;
    cmptr_vrf_proof_export(result->proof, proof_data, &proof_len);
    
    // Import and verify (simulating external verifier)
    cmptr_vrf_proof_t* imported_proof = cmptr_vrf_proof_import(system, proof_data, proof_len);
    
    bool verified = cmptr_vrf_verify(
        system, operator_public,
        (const uint8_t*)lottery_seed, strlen(lottery_seed),
        vrf_output, imported_proof
    );
    
    printf("Proof size: %zu bytes\n", proof_len);
    printf("Verification result: %s\n", verified ? "✓ Valid - Lottery was fair!" : "✗ Invalid - Fraud detected!");
    
    // Cleanup
    cmptr_vrf_proof_free(imported_proof);
    cmptr_vrf_result_free(result);
    cmptr_vrf_secret_free(operator_secret);
    cmptr_vrf_public_free(operator_public);
    cmptr_vrf_system_free(system);
}

int main() {
    printf("=== Cmptr VRF Demo ===\n");
    printf("Verifiable Random Functions without elliptic curves\n");
    printf("Quantum-secure via SHA3-256 only (AXIOM A001)\n\n");
    
    demo_basic_vrf();
    demo_committee_selection();
    demo_lottery_fairness();
    
    printf("\n\n=== Summary ===\n");
    printf("✓ Deterministic randomness with proof\n");
    printf("✓ No elliptic curves or discrete log\n");
    printf("✓ Zero-knowledge proofs via STARKs\n");
    printf("✓ Suitable for consensus, lotteries, gaming\n");
    printf("✓ Post-quantum secure (SHA3-only)\n");
    printf("\nNOTE: This demo uses simulated proofs. Full implementation would:\n");
    printf("- Generate real ~190KB STARK proofs\n");
    printf("- Use BaseFold RAA for proof generation\n");
    printf("- Provide binding and uniqueness guarantees\n");
    
    return 0;
}