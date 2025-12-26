#include "enc.h"
#include "../../sha3/include/sha3.h"
#include "basefold_trace.h"
#include <string.h>

// Global tweaks storage - shared between encoder and verifier
static gf128_t Tweaks[MAX_D];

void enc_init(const uint8_t transcript_root[32])
{
    // Step 1: Derive d non-zero tweaks T₀...T_{d-1} using SHAKE-128(root || j)
    for (size_t j = 0; j < D; ++j) {
        // Create input: transcript_root || j (32 + 8 bytes)
        uint8_t shake_input[40];
        memcpy(shake_input, transcript_root, 32);
        
        // Append j as little-endian 64-bit integer
        uint64_t j_le = j;
        memcpy(shake_input + 32, &j_le, 8);
        
        // Generate 16 bytes using SHAKE-128
        uint8_t tweak_bytes[16];
        int result = shake_xof(SHAKE_128, shake_input, 40, tweak_bytes, 16);
        if (result != 16) {
            // Fallback: should not happen in practice
            memset(tweak_bytes, 0, 16);
            tweak_bytes[0] = 1;  // Ensure non-zero
        }
        
        // Convert to GF(128) element
        gf128_t t = gf128_from_bytes(tweak_bytes);
        
        // Ensure non-zero (probability of zero is 2^-128, but handle it)
        if (gf128_is_zero(t)) {
            t = gf128_one();
        }
        
        Tweaks[j] = t;
    }
    
    // Step 2: Compute tweak_digest = SHA3-256(T₀ || ... || T_{d-1})
    sha3_ctx ctx;
    sha3_init(&ctx, SHA3_256);
    
    for (size_t j = 0; j < D; ++j) {
        uint8_t tweak_bytes[16];
        gf128_to_bytes(Tweaks[j], tweak_bytes);
        sha3_update(&ctx, tweak_bytes, 16);
    }
    
    // Store in global basefold_proof structure
    extern basefold_proof_t basefold_proof;
    sha3_final(&ctx, basefold_proof.tweak_digest, 32);
}

// Getter function for tweaks (used by enc_fold)
gf128_t enc_get_tweak(size_t round_index)
{
    if (round_index >= D) {
        return gf128_one();  // Safe fallback
    }
    return Tweaks[round_index];
}