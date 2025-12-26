/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_NETWORKING_H
#define CMPTR_NETWORKING_H

#include <stdint.h>
#include <stdbool.h>
#include <pthread.h>
#include <netinet/in.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Forward declarations from cmptr_blockchain.h */
struct node;
struct peer;
struct block;
struct transaction;

typedef struct node node_t;
typedef struct peer peer_t;
typedef struct block block_t;
typedef struct transaction transaction_t;

/* Message types for P2P protocol */
typedef enum {
    MSG_HANDSHAKE = 0x01,
    MSG_PING = 0x02,
    MSG_PONG = 0x03,
    MSG_GET_BLOCKS = 0x10,
    MSG_BLOCKS = 0x11,
    MSG_GET_HEADERS = 0x12,
    MSG_HEADERS = 0x13,
    MSG_TRANSACTION = 0x20,
    MSG_BATCH_PROOF = 0x21,
    MSG_BLOCK_ANNOUNCEMENT = 0x30,
    MSG_GET_PEERS = 0x40,
    MSG_PEERS = 0x41,
    MSG_SYNC_REQUEST = 0x50,
    MSG_SYNC_RESPONSE = 0x51,
    MSG_PRUNING_PROOF = 0x60
} message_type_t;

/* Message header */
typedef struct {
    uint32_t magic;          /* Network magic number */
    uint8_t type;           /* Message type */
    uint32_t payload_size;  /* Size of payload */
    uint8_t checksum[4];    /* First 4 bytes of SHA3-256(payload) */
} message_header_t;

/* Handshake message */
typedef struct {
    uint32_t version;        /* Protocol version */
    uint64_t timestamp;      /* Current time */
    uint32_t node_type;      /* Type of node (0-7) */
    uint64_t best_height;    /* Best known block height */
    uint8_t best_hash[32];   /* Best known block hash */
    uint16_t listen_port;    /* Port this node listens on */
} handshake_msg_t;

/* Block request */
typedef struct {
    uint64_t start_height;
    uint32_t count;         /* Max blocks to return */
    bool headers_only;      /* Just headers, not full blocks */
} get_blocks_msg_t;

/* Transaction broadcast */
typedef struct {
    uint8_t tx_data[8192];  /* Serialized transaction */
    uint32_t tx_size;       /* Size of transaction data */
    uint32_t hop_count;     /* How many hops this has traveled */
} transaction_msg_t;

/* Batch proof from aggregator */
typedef struct {
    uint32_t aggregator_id;
    uint32_t tx_count;
    uint8_t batch_proof[190*1024];  /* Recursive proof of batch */
    uint8_t merkle_root[32];
} batch_proof_msg_t;

/* Network manager */
typedef struct network_manager {
    int listen_socket;
    struct sockaddr_in listen_addr;
    
    /* Connection management */
    struct peer** peers;
    uint32_t peer_count;
    uint32_t max_peers;
    pthread_mutex_t peer_mutex;
    
    /* Message handling */
    void (*message_handlers[256])(struct peer*, void*, size_t);
    
    /* Network thread */
    pthread_t accept_thread;
    bool is_running;
    
    /* Node reference */
    struct node* node;
} network_manager_t;

/* Initialize networking */
network_manager_t* network_init(
    node_t* node,
    uint16_t port
);

void network_destroy(network_manager_t* net);

/* Start/stop networking */
bool network_start(network_manager_t* net);
bool network_stop(network_manager_t* net);

/* Peer management */
bool network_connect_to_peer(
    network_manager_t* net,
    const char* address,
    uint16_t port
);

void network_disconnect_peer(
    network_manager_t* net,
    peer_t* peer
);

/* Message sending */
bool network_send_message(
    peer_t* peer,
    message_type_t type,
    const void* data,
    size_t size
);

bool network_broadcast_transaction(
    network_manager_t* net,
    const transaction_t* tx
);

bool network_announce_block(
    network_manager_t* net,
    const block_t* block
);

/* Synchronization */
bool network_request_blocks(
    peer_t* peer,
    uint64_t start_height,
    uint32_t count
);

bool network_request_sync(
    peer_t* peer,
    uint64_t our_height
);

/* Discovery */
bool network_request_peers(peer_t* peer);
void network_share_peers(
    network_manager_t* net,
    peer_t* requesting_peer
);

/* Bandwidth management */
typedef struct {
    uint64_t bytes_sent;
    uint64_t bytes_received;
    uint64_t messages_sent;
    uint64_t messages_received;
    double bandwidth_up_kbps;
    double bandwidth_down_kbps;
} network_stats_t;

network_stats_t network_get_stats(const network_manager_t* net);

/* Message handlers are internal to networking.c */

#ifdef __cplusplus
}
#endif

#endif /* CMPTR_NETWORKING_H */