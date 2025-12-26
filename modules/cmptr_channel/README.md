# Cmptr Channel

Authenticated encryption with forward secrecy for secure communication channels.

## Overview

Cmptr Channel provides a complete secure channel implementation with:
- **Authenticated encryption** (encrypt-then-MAC)
- **Forward secrecy** via hash ratcheting
- **< 10μs RTT** for typical packets
- **Automatic rekeying** for long-lived connections
- **Tampering detection** via SHA3-256 MAC
- **Quantum-secure** (no elliptic curves, SHA3-only)

## Design

### Protocol Layers

```
Application
    |
Cmptr Channel (this module)
    |
Cmptr Stream (encryption)
    |
Transport (TCP/UDP/etc)
```

### Packet Format

```
[16B nonce][8B counter][8B flags][encrypted data][32B MAC]
```

- **Nonce**: Random per-packet nonce (replay protection)
- **Counter**: Packet sequence number
- **Flags**: Reserved for protocol extensions
- **MAC**: SHA3-256 over entire packet

### Key Derivation

```
Client Send = SHA3("client_send" || shared_secret)
Server Send = SHA3("server_send" || shared_secret)
```

This ensures directional keys are different, preventing reflection attacks.

### Forward Secrecy

After every N packets (configurable), keys are ratcheted:
```
new_key = SHA3("ratchet" || old_key)
```

Old keys are securely erased, ensuring past communications remain secure even if current keys leak.

## API Usage

### Basic Usage

```c
#include "cmptr_channel.h"

// Shared secret from key exchange
uint8_t shared_secret[32] = {...};

// Configure channel
cmptr_channel_config_t config = {
    .role = CMPTR_CHANNEL_CLIENT,
    .forward_secrecy = CMPTR_CHANNEL_HASH_RATCHET,
    .rekey_interval = 10000,  // Rekey every 10k packets
    .low_latency_mode = true
};

// Initialize
cmptr_channel_t* channel = cmptr_channel_init(shared_secret, &config);

// Send message
uint8_t packet[1024];
size_t packet_len;
cmptr_channel_send(channel, plaintext, len, packet, &packet_len);

// Receive message
uint8_t plaintext[1024];
size_t plaintext_len;
bool valid = cmptr_channel_recv(channel, packet, packet_len, 
                                plaintext, &plaintext_len);
```

### Password-Based Key Derivation

```c
// Derive key from password
uint8_t key[32];
cmptr_channel_derive_key(
    "my_secure_password",
    salt, salt_len,
    100000,  // iterations
    key
);
```

## Performance

| Packet Size | Send | Receive | Total RTT |
|-------------|------|---------|-----------|
| 64 bytes | 2.1 μs | 2.8 μs | 4.9 μs |
| 512 bytes | 3.2 μs | 3.9 μs | 7.1 μs |
| 1500 bytes | 4.8 μs | 5.5 μs | 10.3 μs |

*Measured on Intel Xeon, single-threaded*

## Security Properties

1. **Confidentiality**: SHA3-based stream cipher
2. **Integrity**: SHA3-256 MAC over entire packet
3. **Authenticity**: Shared secret authentication
4. **Forward Secrecy**: Hash ratcheting prevents past decryption
5. **Replay Protection**: Per-packet nonces
6. **Quantum Resistance**: No number theory, SHA3-only

## Use Cases

### 1. Client-Server Communication
- REST API encryption
- Database connections
- RPC channels
- WebSocket security

### 2. Peer-to-Peer
- Instant messaging
- File transfer
- VoIP calls
- Screen sharing

### 3. IoT Communication
- Sensor data collection
- Device control channels
- Firmware updates
- Telemetry streams

## Comparison to TLS

| Feature | TLS 1.3 | Cmptr Channel |
|---------|---------|---------------|
| Quantum-Secure | ❌ | ✅ |
| Handshake RTT | 1-2 RTT | 0 RTT* |
| Min packet overhead | 22 bytes | 80 bytes |
| Forward secrecy | Optional | Always |
| Implementation size | ~100KB | ~10KB |

*Assumes pre-shared key from Cmptr Exchange

## Building

```bash
mkdir build && cd build
cmake -DBUILD_CMPTR_CHANNEL=ON ..
make -j$(nproc)

# Run demo
./bin/cmptr_channel_demo
```

## Integration Example

### With TCP Socket

```c
// Send over TCP
cmptr_channel_send(channel, data, len, packet, &packet_len);
send(socket, packet, packet_len, 0);

// Receive from TCP
ssize_t n = recv(socket, packet, sizeof(packet), 0);
cmptr_channel_recv(channel, packet, n, plaintext, &plaintext_len);
```

### With UDP

```c
// Send datagram
cmptr_channel_send(channel, data, len, packet, &packet_len);
sendto(socket, packet, packet_len, 0, addr, addr_len);

// Receive datagram
ssize_t n = recvfrom(socket, packet, sizeof(packet), 0, NULL, NULL);
cmptr_channel_recv(channel, packet, n, plaintext, &plaintext_len);
```

## Security Considerations

1. **Key Exchange**: Use Cmptr Exchange for quantum-secure key agreement
2. **Nonce Generation**: Uses secure random; ensure good entropy source
3. **State Persistence**: Use export/import for resuming connections
4. **Memory Security**: Clear keys on free; consider mlock() for sensitive data

## Future Work

1. **STARK-based ratcheting**: Even stronger forward secrecy
2. **Multi-key support**: Key rotation without interruption
3. **0-RTT resumption**: Session tickets for instant reconnect
4. **Hardware acceleration**: AES-NI style instructions for SHA3