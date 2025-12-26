# 🚀 CMPTR Developer Quickstart

Welcome new developer! This guide gets you productive in 15 minutes.

## 🎯 Project Goal
Build a 1 Million TPS blockchain that uses only 3.2GB storage forever (yes, really!)

## ⚡ Get Started in 3 Steps

### Step 1: Clone and Build (2 minutes)
```bash
git clone --recurse-submodules https://github.com/RhettCreighton/gate_computer.git cmptr
cd cmptr
./QUICK_BUILD.sh
```

### Step 2: Run Working Demos (1 minute)
```bash
./build/bin/compile_time_proof_demo   # See compile-time guarantees
./build/bin/verify_truths             # Check 327 system properties
./build/bin/crypto_demo               # Crypto primitives overview
```

### Step 3: Understand the Code (5 minutes)
```bash
# Read in this order:
cat README.md                         # 30-line project overview
cat START_HERE.md                     # Developer guide
cat CLAUDE.md                         # Technical reference
```

## 🔧 What Works vs What Needs Work

### ✅ What Works Today
- **SHA3-256 hashing** with AVX-512 optimization (10x faster!)
- **GF(2^128) arithmetic** for cryptographic operations
- **Truth verification** system with 327 programmatic checks
- **Compile-time proofs** that enforce axioms at build time
- **Basic crypto demos** showing all primitives

### ⚠️ What Needs Integration
- **BaseFold RAA proofs** - Components exist but need connection
- **Binary NTT optimization** - Code written but not integrated
- **Circular recursion** - Examples broken due to API changes
- **Accumulator module** - Missing one source file

### ❌ What's Not Built Yet
- **Network layer** - P2P protocol not implemented
- **Persistence** - No database integration
- **Production binary** - Main cmptr app doesn't compile
- **F* verification** - Proofs exist but need OCaml to run

## 🐛 Common Issues & Fixes

### Issue 1: "sha3_init not found"
**Problem**: Examples use old SHA3 API
**Fix**: Replace with new API:
```c
// OLD (broken):
sha3_ctx ctx;
sha3_init(&ctx, 32);
sha3_update(&ctx, data, len);
sha3_final(hash, &ctx);

// NEW (working):
sha3_hash(SHA3_256, data, len, hash, 32);
```

### Issue 2: "proof_generator.c not found"
**Problem**: Missing source file
**Fix**: Create stub:
```bash
echo "// Stub for proof_generator.c" > modules/cmptr_accumulator/src/proof_generator.c
```

### Issue 3: Build fails with many errors
**Solution**: Use `./BUILD_WORKING_CONFIG.sh` which only builds working modules

## 📊 Project Architecture

```
                    Block Producers (10 nodes)
                    ↑ Recursive proofs (190KB each)
                Proof Generators (100 nodes)  
                    ↑ Batch proofs
                 Aggregators (1000 nodes)
                    ↑ Transactions
                    Users (unlimited)

Total: 1,000 aggregators × 1,000 TPS = 1 Million TPS
```

## 🎯 Your First Contribution

### Option 1: Fix SHA3 API in Examples (Easy - 2 hours)
1. Pick any example in `examples/` that doesn't compile
2. Replace old SHA3 API calls with `sha3_hash()`
3. Test it works
4. Submit PR

### Option 2: Create Missing Stub Files (Easy - 1 hour)
1. Find missing files from build errors
2. Create minimal stub implementations
3. Get more modules building
4. Submit PR

### Option 3: Integrate Binary NTT (Medium - 1 week)
1. Study `modules/basefold/src/binary_ntt_core.c`
2. Connect it to BaseFold RAA in `modules/basefold_raa/`
3. Update examples to use optimized version
4. Submit PR with benchmarks

### Option 4: Fix Circular Recursion (Hard - 2 weeks)
1. Update circular blockchain examples to new SHA3 API
2. Get recursive proof generation working
3. Create end-to-end demo
4. Submit PR with documentation

## 🔑 Key Concepts to Understand

### 1. PARKED vs ACTIVE Tokens
- **PARKED**: Permanent tokens (like HODLing forever)
- **ACTIVE**: Expire after 1 year
- This bounds storage to 3.2GB maximum!

### 2. BaseFold RAA
- Post-quantum secure proof system
- 121-bit security (not 128 due to field limitations)
- ~150ms proof generation, ~190KB proof size

### 3. Truth Bucket System
- 327 programmatic checks about the system
- Run `./build/bin/verify_truths --list` to see all
- Each truth has a verifier in `modules/truth_verifier/src/`

### 4. Compile-Time Proofs
- Critical properties verified at build time
- See `include/compile_time_proofs.h`
- If you violate an axiom, code won't compile!

## 📚 Essential Files to Read

1. **For Architecture**: `docs/guides/FINAL_ARCHITECTURE_SUMMARY.md`
2. **For Crypto**: `modules/README.md` (explains each module)
3. **For Proofs**: `docs/SECURITY_PROOF_MATHEMATICAL.md`
4. **For Truth System**: `modules/truth_verifier/README.md`
5. **For F* Proofs**: `modules/truth_verifier/fstar/README.md`

## 🚦 Development Workflow

1. **Always build with**: `./BUILD_WORKING_CONFIG.sh`
2. **Test changes with**: `./build/bin/verify_truths`
3. **Check proofs with**: `./build/bin/compile_time_proof_demo`
4. **Commit with clear messages** explaining what you fixed

## 💡 Pro Tips

1. **Don't trust old examples** - Many use outdated APIs
2. **Focus on integration** - Components work, they just need connecting
3. **Read the truths** - They document what the system actually does
4. **Ask questions** - File issues on GitHub if stuck
5. **Small PRs welcome** - Even fixing one example helps!

## 🎯 The Big Picture

You're working on a blockchain that solves the trilemma:
- **Scalability**: 1M TPS via hierarchical architecture
- **Security**: 121-bit post-quantum (no elliptic curves!)
- **Decentralization**: 3.2GB storage enables mobile nodes

The core innovation is "forgetting correctly" - using PARKED/ACTIVE tokens and recursive proofs to bound storage forever while maintaining security.

## Need Help?

1. **Build issues**: Check `docs/guides/TROUBLESHOOTING.md`
2. **Architecture questions**: Read truth buckets (T001-T999)
3. **Stuck on something**: File a GitHub issue
4. **Want to chat**: See contact info in README

Welcome aboard! You're helping build the future of scalable blockchains. 🚀