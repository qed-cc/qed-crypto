/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <cmptr_pos.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>

int main(void) {
    printf("=== CMPTR PoS Validator Demo ===\n\n");
    printf("Demonstrating validator lifecycle and operations\n\n");
    
    /* Initialize system */
    blockchain_t* blockchain = cmptr_blockchain_init();
    cmptr_accumulator_t* accumulator = cmptr_accumulator_init();
    pos_state_t* pos = cmptr_pos_init(accumulator, blockchain);
    
    if (!blockchain || !accumulator || !pos) {
        fprintf(stderr, "Failed to initialize\n");
        return 1;
    }
    
    /* Generate validator keys */
    printf("1. Generating validator keys...\n");
    uint8_t public_key[32];
    uint8_t vrf_public[64];
    uint8_t vrf_private[256];
    
    /* Generate identity */
    for (int i = 0; i < 32; i++) {
        public_key[i] = (uint8_t)(0xVA + i); /* VA for validator */
    }
    
    /* Generate VRF keys */
    if (!cmptr_pos_generate_vrf_keys(vrf_public, vrf_private)) {
        fprintf(stderr, "Failed to generate VRF keys\n");
        return 1;
    }
    
    printf("   ✓ Public key: ");
    for (int i = 0; i < 8; i++) {
        printf("%02x", public_key[i]);
    }
    printf("...\n");
    
    printf("   ✓ VRF public: ");
    for (int i = 0; i < 8; i++) {
        printf("%02x", vrf_public[i]);
    }
    printf("...\n");
    
    /* Add validator with stake */
    printf("\n2. Staking 100M tokens...\n");
    uint64_t stake_amount = 100000000; /* 100M tokens */
    
    if (!cmptr_pos_add_validator(pos, public_key, stake_amount, vrf_public)) {
        fprintf(stderr, "Failed to add validator\n");
        return 1;
    }
    
    /* Show pending state */
    validator_pos_t* my_validator = pos->validators[0];
    memcpy(my_validator->vrf_private_key, vrf_private, 256);
    
    printf("   ✓ Validator added\n");
    printf("   - State: PENDING\n");
    printf("   - Activation epoch: %lu\n", my_validator->activation_epoch);
    printf("   - Stake: %lu tokens\n", my_validator->stake_amount);
    
    /* Simulate epoch advancement */
    printf("\n3. Advancing epochs to activate...\n");
    
    for (int i = 0; i < 3; i++) {
        cmptr_pos_advance_epoch(pos);
        printf("   → Epoch %u\n", pos->current_epoch);
        
        if (my_validator->state == STAKE_STATE_ACTIVE) {
            printf("   ✓ Validator ACTIVE!\n");
            break;
        }
    }
    
    /* Create VRF output for committee selection */
    printf("\n4. Computing VRF for committee selection...\n");
    
    uint8_t epoch_seed[32];
    memcpy(epoch_seed, &pos->current_epoch, 4);
    
    lattice_vrf_t* vrf_output = cmptr_pos_compute_vrf(
        vrf_private,
        epoch_seed,
        32
    );
    
    if (vrf_output) {
        printf("   ✓ VRF computed\n");
        printf("   - Output: ");
        for (int i = 0; i < 8; i++) {
            printf("%02x", vrf_output->output[i]);
        }
        printf("...\n");
        printf("   - Proof size: %u bytes\n", vrf_output->proof_size);
        
        /* Verify VRF */
        if (cmptr_pos_verify_vrf(vrf_public, epoch_seed, 32, vrf_output)) {
            printf("   ✓ VRF verified!\n");
        }
        
        free(vrf_output);
    }
    
    /* Update stake */
    printf("\n5. Increasing stake to 150M tokens...\n");
    
    if (cmptr_pos_update_stake(pos, public_key, 150000000)) {
        printf("   ✓ Stake updated: %lu → %lu\n",
               stake_amount, my_validator->stake_amount);
    }
    
    /* Show performance */
    printf("\n6. Validator performance:\n");
    my_validator->blocks_proposed = 42;
    my_validator->blocks_signed = 1337;
    my_validator->blocks_missed = 3;
    my_validator->uptime_percentage = 99.7;
    
    printf("   - Blocks proposed: %lu\n", my_validator->blocks_proposed);
    printf("   - Blocks signed: %lu\n", my_validator->blocks_signed);
    printf("   - Blocks missed: %lu\n", my_validator->blocks_missed);
    printf("   - Uptime: %.1f%%\n", my_validator->uptime_percentage);
    
    /* Start unbonding */
    printf("\n7. Initiating unbonding...\n");
    
    if (cmptr_pos_remove_validator(pos, public_key)) {
        printf("   ✓ Unbonding started\n");
        printf("   - State: UNBONDING\n");
        printf("   - Exit epoch: %lu\n", my_validator->exit_epoch);
        printf("   - Unbonding period: %u epochs\n", pos->unbonding_period);
    }
    
    /* Show slashing example */
    printf("\n8. Slashing conditions:\n");
    printf("   • Equivocation: signing two blocks at same height\n");
    printf("   • Invalid blocks: proposing invalid state transitions\n");
    printf("   • Liveness: missing too many blocks\n");
    
    /* Simulate equivocation evidence */
    uint8_t evidence[128];
    memset(evidence, 0xEV, 128); /* Fake evidence */
    
    printf("\n   ⚠️  Simulating equivocation detection...\n");
    
    /* Create another validator to slash */
    uint8_t bad_validator[32];
    memset(bad_validator, 0xBA, 32);
    cmptr_pos_add_validator(pos, bad_validator, 50000000, vrf_public);
    pos->validators[1]->state = STAKE_STATE_ACTIVE;
    
    if (cmptr_pos_report_equivocation(pos, bad_validator, evidence, 128)) {
        printf("   ✗ Validator SLASHED!\n");
        printf("   - Stake forfeited: 50M tokens\n");
    }
    
    /* Summary */
    printf("\n9. Validator Economics:\n");
    printf("   • Minimum stake: %lu tokens\n", pos->min_stake);
    printf("   • Annual rewards: ~5%% of stake\n");
    printf("   • Unbonding period: %u epochs (~%u days)\n",
           pos->unbonding_period,
           (pos->unbonding_period * 32 * 12) / (3600 * 24)); /* 12s blocks */
    printf("   • Slashing penalty: 100%% of stake\n");
    
    /* Clean up */
    cmptr_pos_destroy(pos);
    cmptr_accumulator_destroy(accumulator);
    cmptr_blockchain_destroy(blockchain);
    
    printf("\n=== Demo Complete ===\n");
    printf("\nValidators secure the network by:\n");
    printf("• Staking tokens as collateral\n");
    printf("• Participating in consensus\n");
    printf("• Producing and validating blocks\n");
    printf("• Maintaining high uptime\n");
    
    return 0;
}