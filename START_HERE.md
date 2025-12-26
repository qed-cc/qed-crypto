# 🚀 CMPTR Project - START HERE

Welcome! CMPTR is a quantum-secure blockchain with bounded storage. This guide shows you EXACTLY what to do.

## ⚡ Quick Facts
- **Goal**: 1 Million TPS blockchain with 3.2GB storage forever
- **Status**: ~80% complete (core works, needs integration)
- **Security**: 121-bit post-quantum (no elliptic curves)
- **Hash**: SHA3-256 ONLY (no exceptions)

## 📁 Project Structure (Simple)

```
cmptr/
├── START_HERE.md         <-- You are here
├── CLAUDE.md            <-- AI developer guide
├── README.md            <-- Project overview
│
├── docs/guides/         <-- All documentation
├── modules/             <-- Core code
├── examples/            <-- Example code
└── build/bin/           <-- Run these:
    ├── crypto_working     ✅ Best demo!
    ├── verify_truths      ✅ 327 checks
    └── sha3_working       ✅ SHA3 demo
```

## 🎯 What To Do First

### 1. Build What Works (5 minutes)
```bash
# Easiest way - use the quick build script:
./QUICK_BUILD.sh

# Or manually:
git submodule update --init modules/sha3 modules/gf128 modules/basefold
mkdir -p build && cd build
cmake -DCMAKE_BUILD_TYPE=Release -DBUILD_BASEFOLD_RAA=ON -DBUILD_TRUTH_VERIFIER=ON ..
make -j$(nproc)
```

### 2. Run Working Demos (2 minutes)
```bash
./build/bin/crypto_demo               # See all crypto primitives
./build/bin/verify_truths             # Check 327 truth statements
./build/bin/compile_time_proof_demo   # NEW! See compile-time proofs
```

### 3. Understand the Project (10 minutes)
Read these IN ORDER:
1. `docs/guides/WHATS_REAL.md` - Separates reality from wishes
2. `docs/guides/WORKING_BUILD_GUIDE.md` - What compiles and runs
3. `modules/truth_verifier/README.md` - How truth system works

## ⚠️ Common Confusions (Avoid These!)

### 1. SHA3 API Changed
```c
// ❌ OLD (in examples): sha3_create_hash_function(SHA3_256)
// ✅ NEW (correct):     sha3_256(data, len, hash)
```

### 2. Performance Claims
- **Claim**: 150ms recursive proofs
- **Reality**: Needs AVX-512 CPU + full implementation
- **Current**: Basic parts work, integration needed

### 3. Missing Modules
Many directories exist but need CMakeLists.txt:
- `circuit_evaluator/` - Not a real module
- `circuit_encoder/` - Not a real module
- Just ignore these

## 📋 Development Priorities

### If You Want Quick Win:
1. Fix SHA3 API in examples
2. Make `examples/sha3_only_demo.c` work
3. Update `examples/basefold_128bit_demo.c`

### If You Want Big Impact:
1. Integrate Binary NTT into BaseFold RAA
2. Fix circular recursion examples
3. Get cmptr binary compiling

### If You Want to Understand:
1. Run `./bin/verify_truths -v`
2. Read truth definitions in `modules/truth_verifier/src/`
3. Check F* proofs in `modules/truth_verifier/fstar/`

## 🔗 Key Resources

| What | Where | Status |
|------|-------|--------|
| **Working Examples** | `build/bin/crypto_demo` | ✅ RUNS |
| **Truth System** | `build/bin/verify_truths` | ✅ RUNS |
| **SHA3 Correct Usage** | `modules/sha3/include/sha3.h` | ✅ WORKS |
| **Developer Guide** | `docs/guides/NEXT_CLAUDE_DEVELOPER_GUIDE.md` | 📖 READ |
| **Build Issues** | `docs/guides/WORKING_BUILD_GUIDE.md` | 🔧 HELPS |

## 💡 The Big Picture

CMPTR solves blockchain's storage problem:
1. **PARKED tokens**: Never expire (like Bitcoin HODLing)
2. **ACTIVE tokens**: Expire after 1 year
3. **Result**: Blockchain size bounded to 3.2GB forever!

Plus:
- 1 Million TPS via hierarchical nodes
- Quantum-secure (no elliptic curves)
- Zero-knowledge always (privacy default)

## 🚦 Next Steps

1. **Build and run** the working demos
2. **Pick one thing** to fix (see priorities above)
3. **Use truth system** to verify your changes
4. **Don't create new files** - fix what exists

Remember: The hard cryptography is DONE. It just needs assembly!

---
Questions? The truth system has answers: `./bin/verify_truths --list`