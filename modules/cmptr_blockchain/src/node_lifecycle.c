/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_blockchain.h"
#include <stdio.h>

/* Stop node */
bool cmptr_blockchain_stop_node(node_t* node) {
    if (!node) return false;
    
    /* Check if already stopped */
    if (node->state == NODE_STATE_SHUTTING_DOWN) {
        return true;
    }
    
    /* Set state to shutting down */
    node->state = NODE_STATE_SHUTTING_DOWN;
    
    /* Stop node-specific operations */
    switch (node->type) {
        case NODE_TYPE_AGGREGATOR:
            printf("Stopping Aggregator #%u\n", node->data.aggregator.id);
            break;
            
        case NODE_TYPE_GENERATOR:
            printf("Stopping Generator #%u\n", node->data.generator.id);
            break;
            
        case NODE_TYPE_PRODUCER:
            printf("Stopping Producer #%u\n", node->data.producer.id);
            break;
            
        case NODE_TYPE_VALIDATOR:
            printf("Stopping Validator\n");
            break;
            
        default:
            break;
    }
    
    /* Stop networking if running */
    /* In real implementation, would stop network threads */
    
    return true;
}

/* Get node state */
node_state_t cmptr_blockchain_get_node_state(const node_t* node) {
    if (!node) return NODE_STATE_SHUTTING_DOWN;
    return node->state;
}

/* Connect to peer */
bool cmptr_blockchain_connect_peer(
    node_t* node,
    const char* address,
    uint16_t port
) {
    if (!node || !address) return false;
    
    printf("Node connecting to peer %s:%u\n", address, port);
    
    /* In real implementation, would establish connection */
    
    return true;
}

/* Disconnect peer */
bool cmptr_blockchain_disconnect_peer(
    node_t* node,
    const peer_t* peer
) {
    if (!node || !peer) return false;
    
    printf("Disconnecting peer %s:%u\n", peer->address, peer->port);
    
    /* In real implementation, would close connection */
    
    return true;
}

/* Get peer count */
uint32_t cmptr_blockchain_get_peer_count(const node_t* node) {
    if (!node) return 0;
    return node->peer_count;
}