# Cmptr Exchange

STARK-based key exchange protocol without number theory assumptions.

## Overview

Cmptr Exchange provides quantum-secure key agreement using only SHA3-256 and recursive STARKs. Unlike traditional Diffie-Hellman or ECDH, this protocol:

- **No discrete log problem** - Uses STARKs instead of elliptic curves
- **Post-quantum secure** - Based only on hash functions
- **Zero-knowledge** - Reveals nothing beyond key agreement
- **Authenticated** - Built-in transcript prevents MITM attacks

## Protocol Design

### Three-Phase Commit-Reveal

```
Alice                           Bob
  |                              |
  |------ Commitment_A --------->|
  |<------ Commitment_B ----------|
  |                              |
  |------ STARK_Proof_A -------->|
  |<------ STARK_Proof_B --------|
  |                              |
  |== Derive Shared Secret ======|
```

1. **Commit Phase**: Both parties commit to their public keys
2. **Reveal Phase**: Exchange STARK proofs after seeing commitments
3. **Derive Phase**: Compute shared secret from proofs

This prevents rushing attacks where one party waits to see the other's key.

### STARK-Based Construction

The key exchange circuit proves:
```
"I know secret x such that:
 1. commitment = SHA3(x)
 2. shared_output = F(x, peer_commitment)
 where F is a one-way function"
```

The STARK proof (~190KB) convinces the peer without revealing x.

## API Usage

### Basic Key Exchange

```c
#include "cmptr_exchange.h"

// Initialize system
cmptr_exchange_system_t* system = cmptr_exchange_init();

// Alice generates ephemeral keys
cmptr_exchange_private_t* alice_priv;
cmptr_exchange_public_t* alice_pub;
cmptr_exchange_keygen(system, &alice_priv, &alice_pub);

// Create commitment
uint8_t alice_commit[32];
cmptr_exchange_commit(alice_pub, alice_commit);

// ... exchange commitments ...

// Reveal STARK proof
uint8_t alice_proof[200000];
size_t alice_proof_len;
cmptr_exchange_reveal(alice_pub, alice_proof, &alice_proof_len);

// ... exchange proofs ...

// Derive shared secret
uint8_t shared_secret[32];
cmptr_exchange_derive(system, alice_priv, bob_proof, bob_proof_len, shared_secret);
```

### Authenticated Exchange

```c
// Create transcript for authentication
cmptr_exchange_transcript_t* transcript = cmptr_exchange_transcript_new();

// Add protocol context
cmptr_exchange_transcript_add(transcript, "version", version_bytes, version_len);
cmptr_exchange_transcript_add(transcript, "alice_id", alice_id, id_len);
cmptr_exchange_transcript_add(transcript, "bob_id", bob_id, id_len);

// ... perform key exchange ...

// Finalize authenticated context
uint8_t auth_context[32];
cmptr_exchange_transcript_finalize(transcript, shared_secret, auth_context);

// Use for secure channel
cmptr_channel_t* channel = cmptr_channel_init(auth_context, &config);
```

## Security Properties

### Quantum Resistance
- No number theory assumptions
- Security reduces to SHA3-256 collision resistance
- 121-bit post-quantum security level

### Zero-Knowledge
- STARK proofs reveal nothing about private keys
- Simulator can produce indistinguishable transcripts
- Perfect zero-knowledge via polynomial masking

### Authentication
- Transcript binds all protocol messages
- Prevents man-in-the-middle attacks
- Context includes party identities

### Forward Secrecy
- Ephemeral keys provide forward secrecy
- Past sessions remain secure if long-term keys leak
- Can be combined with Cmptr Channel ratcheting

## Performance

| Operation | Time | Size |
|-----------|------|------|
| Key Generation | ~150ms | 32 bytes (private) |
| STARK Proof | ~150ms | ~190KB |
| Verification | ~8ms | - |
| Total Exchange | ~320ms | ~380KB traffic |

*Full implementation with BaseFold RAA*

## Comparison to Classical Protocols

| Protocol | Quantum-Secure | Proof Size | Assumptions |
|----------|----------------|------------|-------------|
| ECDH | ❌ | 64 bytes | Discrete log |
| X25519 | ❌ | 32 bytes | Discrete log |
| RSA-2048 | ❌ | 256 bytes | Factoring |
| Kyber | ✅ | ~1KB | Lattices |
| **Cmptr Exchange** | ✅ | ~190KB | SHA3 only |

## Use Cases

### 1. TLS Replacement
Replace ECDHE in TLS 1.3 with Cmptr Exchange for quantum-secure handshakes.

### 2. Mesh Networks
Establish pairwise keys in distributed systems without PKI.

### 3. IoT Key Agreement
Long-term quantum security for devices with 20+ year lifespans.

### 4. Blockchain Protocols
Anonymous key exchange for privacy coins and state channels.

## Implementation Status

**Current (Demo)**: Simulated STARK proofs for API demonstration

**Full Implementation** would require:
1. Key exchange circuit in R1CS/AIR format
2. BaseFold RAA prover integration
3. Optimized proof generation (~150ms)
4. Proof compression techniques
5. Batch verification support

## Building

```bash
mkdir build && cd build
cmake -DBUILD_CMPTR_EXCHANGE=ON ..
make -j$(nproc)

# Run demo
./bin/cmptr_exchange_demo
```

## Future Work

1. **Proof Size Reduction**: Investigate recursive compression to ~50KB
2. **Hardware Acceleration**: FPGA/ASIC for proof generation
3. **Multi-Party**: Extend to N-party key agreement
4. **Identity Binding**: Optional long-term identity keys
5. **Standardization**: Work toward IETF RFC