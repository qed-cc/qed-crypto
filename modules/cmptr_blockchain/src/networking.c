/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "networking.h"
#include "cmptr_blockchain.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <errno.h>

/* Network magic number for cmptr blockchain */
#define CMPTR_MAGIC 0x434D5054  /* "CMPT" */

/* Forward declarations for message handlers */
static void handle_handshake(struct peer* peer, void* data, size_t size);
static void handle_ping(struct peer* peer, void* data, size_t size);
static void handle_transaction(struct peer* peer, void* data, size_t size);
static void handle_block_announcement(struct peer* peer, void* data, size_t size);

/* Initialize networking */
network_manager_t* network_init(node_t* node, uint16_t port) {
    network_manager_t* net = calloc(1, sizeof(network_manager_t));
    if (!net) return NULL;
    
    net->node = node;
    net->max_peers = node->network_config.max_peers;
    net->peers = (struct peer**)calloc(net->max_peers, sizeof(struct peer*));
    pthread_mutex_init(&net->peer_mutex, NULL);
    
    /* Create listen socket */
    net->listen_socket = socket(AF_INET, SOCK_STREAM, 0);
    if (net->listen_socket < 0) {
        free(net->peers);
        free(net);
        return NULL;
    }
    
    /* Allow socket reuse */
    int opt = 1;
    setsockopt(net->listen_socket, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
    
    /* Bind to port */
    net->listen_addr.sin_family = AF_INET;
    net->listen_addr.sin_addr.s_addr = INADDR_ANY;
    net->listen_addr.sin_port = htons(port);
    
    if (bind(net->listen_socket, (struct sockaddr*)&net->listen_addr, 
             sizeof(net->listen_addr)) < 0) {
        close(net->listen_socket);
        free(net->peers);
        free(net);
        return NULL;
    }
    
    /* Listen for connections */
    if (listen(net->listen_socket, 10) < 0) {
        close(net->listen_socket);
        free(net->peers);
        free(net);
        return NULL;
    }
    
    /* Register message handlers */
    net->message_handlers[MSG_HANDSHAKE] = handle_handshake;
    net->message_handlers[MSG_PING] = handle_ping;
    net->message_handlers[MSG_TRANSACTION] = handle_transaction;
    net->message_handlers[MSG_BLOCK_ANNOUNCEMENT] = handle_block_announcement;
    
    printf("Network initialized on port %u\n", port);
    
    return net;
}

/* Accept thread */
static void* accept_thread(void* arg) {
    network_manager_t* net = (network_manager_t*)arg;
    
    while (net->is_running) {
        struct sockaddr_in peer_addr;
        socklen_t addr_len = sizeof(peer_addr);
        
        int peer_socket = accept(net->listen_socket, 
                               (struct sockaddr*)&peer_addr, &addr_len);
        
        if (peer_socket < 0) {
            if (errno != EINTR) {
                perror("accept");
            }
            continue;
        }
        
        /* Create peer structure */
        pthread_mutex_lock(&net->peer_mutex);
        
        if (net->peer_count < net->max_peers) {
            struct peer* peer = calloc(1, sizeof(struct peer));
            inet_ntop(AF_INET, &peer_addr.sin_addr, peer->address, 256);
            peer->port = ntohs(peer_addr.sin_port);
            peer->socket_fd = peer_socket;
            peer->is_outbound = false;
            peer->last_seen = time(NULL);
            
            net->peers[net->peer_count++] = peer;
            
            printf("Accepted connection from %s:%u\n", peer->address, peer->port);
            
            /* Start peer thread */
            /* In real implementation, would handle peer communication */
        } else {
            close(peer_socket);
        }
        
        pthread_mutex_unlock(&net->peer_mutex);
    }
    
    return NULL;
}

/* Start networking */
bool network_start(network_manager_t* net) {
    if (!net || net->is_running) return false;
    
    net->is_running = true;
    
    /* Start accept thread */
    if (pthread_create(&net->accept_thread, NULL, accept_thread, net) != 0) {
        net->is_running = false;
        return false;
    }
    
    return true;
}

/* Stop networking */
bool network_stop(network_manager_t* net) {
    if (!net || !net->is_running) return false;
    
    net->is_running = false;
    
    /* Close listen socket to wake accept thread */
    shutdown(net->listen_socket, SHUT_RDWR);
    close(net->listen_socket);
    
    /* Wait for accept thread */
    pthread_join(net->accept_thread, NULL);
    
    /* Disconnect all peers */
    pthread_mutex_lock(&net->peer_mutex);
    for (uint32_t i = 0; i < net->peer_count; i++) {
        if (net->peers[i]) {
            close(net->peers[i]->socket_fd);
            free(net->peers[i]);
        }
    }
    pthread_mutex_unlock(&net->peer_mutex);
    
    return true;
}

/* Destroy networking */
void network_destroy(network_manager_t* net) {
    if (!net) return;
    
    if (net->is_running) {
        network_stop(net);
    }
    
    pthread_mutex_destroy(&net->peer_mutex);
    free(net->peers);
    free(net);
}

/* Message handlers (stubs) */
static void handle_handshake(struct peer* peer, void* data, size_t size) {
    printf("Received handshake from %s\n", peer->address);
}

static void handle_ping(struct peer* peer, void* data, size_t size) {
    /* Send pong */
}

static void handle_transaction(struct peer* peer, void* data, size_t size) {
    printf("Received transaction from %s\n", peer->address);
}

static void handle_block_announcement(struct peer* peer, void* data, size_t size) {
    printf("Received block announcement from %s\n", peer->address);
}

/* Get network stats */
network_stats_t network_get_stats(const network_manager_t* net) {
    network_stats_t stats = {0};
    
    if (!net) return stats;
    
    /* In real implementation, would track actual bandwidth */
    stats.bytes_sent = 0;
    stats.bytes_received = 0;
    stats.messages_sent = 0;
    stats.messages_received = 0;
    
    return stats;
}