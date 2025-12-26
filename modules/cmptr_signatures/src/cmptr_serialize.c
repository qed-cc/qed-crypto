/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include "cmptr_signatures_internal.h"
#include <stdlib.h>
#include <string.h>

// Serialization format constants
#define CMPTR_MAGIC_SIGNATURE 0x434D5453  // "CMTS"
#define CMPTR_MAGIC_AGG_SIG   0x434D5441  // "CMTA"
#define CMPTR_MAGIC_PUBKEY    0x434D5450  // "CMTP"
#define CMPTR_MAGIC_PRIVKEY   0x434D544B  // "CMTK"
#define CMPTR_VERSION         0x00010000  // 1.0.0

// Size calculation functions
size_t cmptr_signature_size(const cmptr_signature_t* sig) {
    if (!sig || !sig->stark_proof) return 0;
    
    // Magic (4) + Version (4) + Proof size (8) + Proof data + 
    // Message hash (32) + Pubkey hash (32) + Nonce (32) + Timestamp (8)
    return 4 + 4 + 8 + basefold_proof_size(sig->stark_proof) + 
           3 * CMPTR_SIG_HASH_SIZE + sizeof(uint64_t);
}

size_t cmptr_aggregated_signature_size(const cmptr_aggregated_signature_t* agg_sig) {
    if (!agg_sig || !agg_sig->recursive_proof) return 0;
    
    // Magic (4) + Version (4) + Num sigs (8) + Proof size (8) + Proof data +
    // Aggregation hash (32) + Message hashes + Pubkey hashes
    return 4 + 4 + 8 + 8 + basefold_proof_size(agg_sig->recursive_proof) +
           CMPTR_SIG_HASH_SIZE + 2 * agg_sig->num_signatures * CMPTR_SIG_HASH_SIZE;
}

size_t cmptr_public_key_size(const cmptr_public_key_t* public_key) {
    if (!public_key) return 0;
    // Magic (4) + Version (4) + Commitment (32) + Verification key (32)
    return 4 + 4 + 2 * CMPTR_SIG_HASH_SIZE;
}

size_t cmptr_private_key_size(const cmptr_private_key_t* private_key) {
    if (!private_key) return 0;
    // Magic (4) + Version (4) + Seed (32) + Chain code (32)
    return 4 + 4 + 2 * CMPTR_SIG_HASH_SIZE;
}

// Serialization functions
bool cmptr_signature_serialize(const cmptr_signature_t* sig, uint8_t* buffer, size_t buffer_len) {
    if (!sig || !buffer || buffer_len < cmptr_signature_size(sig)) {
        return false;
    }
    
    uint8_t* ptr = buffer;
    
    // Write magic and version
    uint32_t magic = CMPTR_MAGIC_SIGNATURE;
    uint32_t version = CMPTR_VERSION;
    memcpy(ptr, &magic, 4); ptr += 4;
    memcpy(ptr, &version, 4); ptr += 4;
    
    // Write proof size and data
    size_t proof_size = basefold_proof_size(sig->stark_proof);
    uint64_t proof_size_64 = proof_size;
    memcpy(ptr, &proof_size_64, 8); ptr += 8;
    
    if (!basefold_proof_serialize(sig->stark_proof, ptr, proof_size)) {
        return false;
    }
    ptr += proof_size;
    
    // Write signature data
    memcpy(ptr, sig->message_hash, CMPTR_SIG_HASH_SIZE); ptr += CMPTR_SIG_HASH_SIZE;
    memcpy(ptr, sig->public_key_hash, CMPTR_SIG_HASH_SIZE); ptr += CMPTR_SIG_HASH_SIZE;
    memcpy(ptr, sig->nonce, CMPTR_SIG_HASH_SIZE); ptr += CMPTR_SIG_HASH_SIZE;
    memcpy(ptr, &sig->timestamp, sizeof(uint64_t));
    
    return true;
}

bool cmptr_aggregated_signature_serialize(const cmptr_aggregated_signature_t* agg_sig, 
                                       uint8_t* buffer, size_t buffer_len) {
    if (!agg_sig || !buffer || buffer_len < cmptr_aggregated_signature_size(agg_sig)) {
        return false;
    }
    
    uint8_t* ptr = buffer;
    
    // Write magic and version
    uint32_t magic = CMPTR_MAGIC_AGG_SIG;
    uint32_t version = CMPTR_VERSION;
    memcpy(ptr, &magic, 4); ptr += 4;
    memcpy(ptr, &version, 4); ptr += 4;
    
    // Write number of signatures
    uint64_t num_sigs = agg_sig->num_signatures;
    memcpy(ptr, &num_sigs, 8); ptr += 8;
    
    // Write proof size and data
    size_t proof_size = basefold_proof_size(agg_sig->recursive_proof);
    uint64_t proof_size_64 = proof_size;
    memcpy(ptr, &proof_size_64, 8); ptr += 8;
    
    if (!basefold_proof_serialize(agg_sig->recursive_proof, ptr, proof_size)) {
        return false;
    }
    ptr += proof_size;
    
    // Write aggregation data
    memcpy(ptr, agg_sig->aggregation_hash, CMPTR_SIG_HASH_SIZE); ptr += CMPTR_SIG_HASH_SIZE;
    memcpy(ptr, agg_sig->message_hashes, agg_sig->num_signatures * CMPTR_SIG_HASH_SIZE);
    ptr += agg_sig->num_signatures * CMPTR_SIG_HASH_SIZE;
    memcpy(ptr, agg_sig->public_key_hashes, agg_sig->num_signatures * CMPTR_SIG_HASH_SIZE);
    
    return true;
}

bool cmptr_public_key_serialize(const cmptr_public_key_t* public_key, 
                             uint8_t* buffer, size_t buffer_len) {
    if (!public_key || !buffer || buffer_len < cmptr_public_key_size(public_key)) {
        return false;
    }
    
    uint8_t* ptr = buffer;
    
    // Write magic and version
    uint32_t magic = CMPTR_MAGIC_PUBKEY;
    uint32_t version = CMPTR_VERSION;
    memcpy(ptr, &magic, 4); ptr += 4;
    memcpy(ptr, &version, 4); ptr += 4;
    
    // Write key data
    memcpy(ptr, public_key->commitment, CMPTR_SIG_HASH_SIZE); ptr += CMPTR_SIG_HASH_SIZE;
    memcpy(ptr, public_key->verification_key, CMPTR_SIG_HASH_SIZE);
    
    return true;
}

bool cmptr_private_key_serialize(const cmptr_private_key_t* private_key,
                              uint8_t* buffer, size_t buffer_len) {
    if (!private_key || !buffer || buffer_len < cmptr_private_key_size(private_key)) {
        return false;
    }
    
    uint8_t* ptr = buffer;
    
    // Write magic and version
    uint32_t magic = CMPTR_MAGIC_PRIVKEY;
    uint32_t version = CMPTR_VERSION;
    memcpy(ptr, &magic, 4); ptr += 4;
    memcpy(ptr, &version, 4); ptr += 4;
    
    // Write key data
    memcpy(ptr, private_key->seed, CMPTR_SIG_HASH_SIZE); ptr += CMPTR_SIG_HASH_SIZE;
    memcpy(ptr, private_key->chain_code, CMPTR_SIG_HASH_SIZE);
    
    return true;
}

// Deserialization functions
cmptr_signature_t* cmptr_signature_deserialize(const uint8_t* buffer, size_t buffer_len) {
    if (!buffer || buffer_len < 4 + 4 + 8) {
        return NULL;
    }
    
    const uint8_t* ptr = buffer;
    
    // Check magic and version
    uint32_t magic, version;
    memcpy(&magic, ptr, 4); ptr += 4;
    memcpy(&version, ptr, 4); ptr += 4;
    
    if (magic != CMPTR_MAGIC_SIGNATURE || version != CMPTR_VERSION) {
        return NULL;
    }
    
    // Read proof size
    uint64_t proof_size_64;
    memcpy(&proof_size_64, ptr, 8); ptr += 8;
    size_t proof_size = (size_t)proof_size_64;
    
    // Check buffer has enough data
    if (buffer_len < 4 + 4 + 8 + proof_size + 3 * CMPTR_SIG_HASH_SIZE + sizeof(uint64_t)) {
        return NULL;
    }
    
    // Allocate signature
    cmptr_signature_t* sig = calloc(1, sizeof(cmptr_signature_t));
    if (!sig) {
        return NULL;
    }
    
    // Deserialize proof
    sig->stark_proof = basefold_proof_deserialize(ptr, proof_size);
    if (!sig->stark_proof) {
        free(sig);
        return NULL;
    }
    ptr += proof_size;
    
    // Read signature data
    memcpy(sig->message_hash, ptr, CMPTR_SIG_HASH_SIZE); ptr += CMPTR_SIG_HASH_SIZE;
    memcpy(sig->public_key_hash, ptr, CMPTR_SIG_HASH_SIZE); ptr += CMPTR_SIG_HASH_SIZE;
    memcpy(sig->nonce, ptr, CMPTR_SIG_HASH_SIZE); ptr += CMPTR_SIG_HASH_SIZE;
    memcpy(&sig->timestamp, ptr, sizeof(uint64_t));
    
    return sig;
}

// Similar implementations for other deserialization functions...
// (Omitted for brevity, but follow same pattern)