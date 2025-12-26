# QED_CRYPTO - Quantum-Secure Blockchain

**Goal**: 1 Million TPS blockchain with only 3.2GB storage forever.

## Quick Start

```bash
# Build
./BUILD_WORKING_CONFIG.sh

# Run demo
./build/bin/crypto_working
```

## What Works
- ✅ SHA3-256 hashing (AVX-512 optimized)
- ✅ GF(2^128) field arithmetic
- ✅ 327 programmatic truth checks
- ⚠️ Basic proof system (needs integration)

## Key Innovation
**PARKED/ACTIVE tokens**: PARKED tokens never expire (like Bitcoin HODLing), ACTIVE tokens expire after 1 year. Result: blockchain storage bounded to 3.2GB forever!

## Status
~80% designed, ~40% implemented, ~20% integrated. Core cryptography works, needs assembly.

## 📚 Documentation

### For New Developers
- **Quick Start**: [`docs/DEVELOPER_QUICKSTART.md`](docs/DEVELOPER_QUICKSTART.md) - Get productive in 15 minutes
- **Architecture**: [`docs/ARCHITECTURE_VISUAL.md`](docs/ARCHITECTURE_VISUAL.md) - Visual system overview  
- **Troubleshooting**: [`docs/TROUBLESHOOTING.md`](docs/TROUBLESHOOTING.md) - Common issues & fixes
- **Roadmap**: [`ROADMAP.md`](ROADMAP.md) - What needs to be built

### Reference
- **Start Guide**: [`START_HERE.md`](START_HERE.md) - First time setup
- **AI Guide**: [`CLAUDE.md`](CLAUDE.md) - For AI assistants
- **All Docs**: [`docs/`](docs/) - Everything else

## License
Apache 2.0