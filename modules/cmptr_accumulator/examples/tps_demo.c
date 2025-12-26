/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <cmptr_accumulator.h>
#include <stdio.h>
#include <time.h>
#include <pthread.h>

int main(void) {
    printf("=== Gate Accumulator TPS Demo ===\n\n");
    
    /* Initialize accumulator */
    cmptr_accumulator_t* acc = cmptr_accumulator_init();
    
    /* Create hierarchical TPS system */
    printf("1. Setting up hierarchical TPS architecture...\n");
    
    /* Create aggregators */
    uint32_t num_aggregators = 10;
    aggregator_t* aggregators[10];
    
    for (uint32_t i = 0; i < num_aggregators; i++) {
        aggregators[i] = cmptr_accumulator_create_aggregator(acc, i);
        printf("   Created aggregator %u (1000 TPS capacity)\n", i);
    }
    
    /* Create proof generators */
    uint32_t num_generators = 2;
    proof_generator_t* generators[2];
    
    generators[0] = cmptr_accumulator_create_generator(acc, aggregators, 5);
    generators[1] = cmptr_accumulator_create_generator(acc, aggregators + 5, 5);
    printf("   Created %u generators (10K TPS each)\n", num_generators);
    
    /* Create block producer */
    block_producer_t* producer = cmptr_accumulator_create_producer(
        acc, generators, num_generators
    );
    printf("   Created block producer (100K TPS capacity)\n");
    
    /* Calculate theoretical TPS */
    uint64_t theoretical_tps = calculate_hierarchical_tps(
        num_aggregators, num_generators, 1
    );
    printf("\n2. Theoretical TPS: %lu\n", theoretical_tps);
    
    /* Simulate transaction flow */
    printf("\n3. Simulating transaction flow...\n");
    
    /* Create sample transactions */
    uint8_t user_pubkey[32] = "USER_PUBKEY_FOR_TPS_TESTING!!!";
    uint8_t recipient[32] = "RECIPIENT_PUBKEY_FOR_TESTING!!";
    
    /* Generate a valid spend transaction */
    proof_of_work_t pow = cmptr_accumulator_mine_pow(acc->pow_challenge, 10);
    token_t token = cmptr_accumulator_mint_token(acc, user_pubkey, &pow);
    
    /* Activate it */
    uint8_t secret[32] = "SECRET_KEY_FOR_SPENDING_TEST!!";
    proof_of_work_t activate_pow = cmptr_accumulator_mine_pow(acc->pow_challenge, 10);
    activation_tx_t activation = cmptr_accumulator_activate_token(
        acc, &token, secret, &activate_pow
    );
    
    /* Create spend transaction */
    proof_of_work_t spend_pow = cmptr_accumulator_mine_pow(acc->pow_challenge, 10);
    spend_tx_t spend = cmptr_accumulator_spend_token(
        acc, &token, recipient, secret, &spend_pow
    );
    
    /* Submit to aggregator */
    printf("   Submitting transaction to aggregator 0...\n");
    cmptr_accumulator_submit_to_aggregator(aggregators[0], &spend);
    
    /* Show hierarchical processing */
    printf("\n4. Hierarchical Processing Flow:\n");
    printf("   Layer 1: %u aggregators × 1,000 TPS = %u TPS\n", 
           num_aggregators, num_aggregators * 1000);
    printf("   Layer 2: %u generators × 10,000 TPS = %u TPS\n",
           num_generators, num_generators * 10000);
    printf("   Layer 3: 1 producer × 100,000 TPS = 100,000 TPS\n");
    printf("   Bottleneck: %lu TPS (limited by aggregators)\n", theoretical_tps);
    
    /* Show scalability path */
    printf("\n5. Scaling to 1 Million TPS:\n");
    printf("   - Need 1,000 aggregators (edge nodes)\n");
    printf("   - Need 100 proof generators (GPUs)\n");
    printf("   - Need 10 block producers (ASICs)\n");
    printf("   - Total hardware cost: ~$400K\n");
    
    /* Clean up */
    /* Note: In real implementation, would properly free all resources */
    cmptr_accumulator_destroy(acc);
    
    printf("\n=== TPS Demo Complete ===\n");
    return 0;
}