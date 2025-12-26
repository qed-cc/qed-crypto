# 🔨 CMPTR Working Build Guide

This guide shows ONLY what actually builds and runs. No wishes, just reality.

## ✅ Build Commands That WORK

### Minimal Working Build
```bash
# From project root - THIS WORKS:
git submodule update --init modules/sha3 modules/gf128 modules/basefold
mkdir -p build && cd build
cmake -DCMAKE_BUILD_TYPE=Release \
      -DBUILD_BASEFOLD_RAA=ON \
      -DBUILD_TRUTH_VERIFIER=ON \
      -DBUILD_CMPTR_ACCUMULATOR=OFF \
      -DBUILD_CMPTR_BLOCKCHAIN=OFF \
      -DBUILD_CMPTR_POS=OFF \
      -DBUILD_FORMAL_PROOF_CIRCUITS=OFF \
      -DBUILD_CMPTR_SIGNATURES=OFF \
      -DBUILD_CMPTR_STREAM=OFF \
      -DBUILD_CMPTR_CHANNEL=OFF \
      -DBUILD_CMPTR_EXCHANGE=OFF \
      -DBUILD_CMPTR_VRF=OFF \
      -DBUILD_CMPTR_TREES=OFF \
      -DBUILD_CMPTR_COMMITMENTS=OFF ..
make -j$(nproc)
```

### What You Get
```bash
build/
├── bin/
│   ├── crypto_demo       ✅ WORKS - Crypto primitives demo
│   ├── verify_truths     ✅ WORKS - Truth verification  
│   └── count_gate_types  ✅ WORKS - Circuit analyzer
└── lib/
    ├── libsha3.a         ✅ SHA3 hashing
    ├── libgf128.a        ✅ Field arithmetic
    ├── libcommon.a       ✅ Utilities
    └── libtruth_verifier.a ✅ Truth system
```

## ❌ Build Commands That FAIL

### Don't Try These (Missing Dependencies)
```bash
# These will ALL FAIL:
-DBUILD_CMPTR_BLOCKCHAIN=ON    # Missing: aggregator.c, generator.c
-DBUILD_CMPTR_ACCUMULATOR=ON   # Missing: proof_generator.c
-DBUILD_CMPTR_POS=ON          # Missing: proof_triggers.c
-DBUILD_CMPTR_SIGNATURES=ON   # Missing: test files
-DBUILD_FORMAL_PROOF_CIRCUITS=ON # Missing: basefold_raa config
```

## 🔧 Fixing Common Build Errors

### Error: "sha3.h not found"
```bash
# You forgot submodules:
git submodule update --init modules/sha3 modules/gf128 modules/basefold
```

### Error: "No such file or directory" 
```bash
# You're in wrong directory. Always build from project root:
cd /path/to/cmptr
mkdir -p build && cd build
```

### Error: "undefined reference to register_proof_timing_truths"
```bash
# This is already fixed in main.c - pull latest
```

## 📦 Module Status

| Module | Builds? | Runs? | Why It Fails |
|--------|---------|-------|--------------|
| sha3 | ✅ | ✅ | - |
| gf128 | ✅ | ✅ | - |
| basefold | ✅ | ✅ | - |
| basefold_raa | ✅ | ⚠️ | Examples broken |
| truth_verifier | ✅ | ✅ | - |
| cmptr_accumulator | ❌ | ❌ | Missing files |
| cmptr_blockchain | ❌ | ❌ | Missing files |
| cmptr_pos | ❌ | ❌ | Missing files |
| cmptr_signatures | ❌ | ❌ | Missing tests |

## 🎯 Working Examples

### 1. Crypto Demo (WORKS!)
```bash
./build/bin/crypto_demo

# Shows:
# - SHA3 hashing
# - Field operations  
# - Merkle trees
# - Performance stats
```

### 2. Truth Verifier (WORKS!)
```bash
# List all 327 truths
./build/bin/verify_truths --list

# Check specific truth
./build/bin/verify_truths --id T001

# Verbose output
./build/bin/verify_truths -v
```

### 3. Simple SHA3 Test (WORKS!)
```c
// test_sha3.c
#include <stdio.h>
#include <string.h>
#include "sha3.h"

int main() {
    uint8_t hash[32];
    const char* msg = "Hello CMPTR!";
    
    // Direct API - THIS WORKS
    sha3_256((uint8_t*)msg, strlen(msg), hash);
    
    printf("SHA3-256: ");
    for(int i = 0; i < 32; i++) {
        printf("%02x", hash[i]);
    }
    printf("\n");
    return 0;
}
```

Compile:
```bash
gcc test_sha3.c -Imodules/sha3/include -Lbuild/lib -lsha3 -o test_sha3
./test_sha3
```

## ⚡ Quick Fixes

### Make Examples Work
Most examples use old SHA3 API. Fix:
```c
// OLD (broken):
sha3_hash_function* h = sha3_create_hash_function(SHA3_256);

// NEW (works):
uint8_t hash[32];
sha3_256(data, len, hash);
```

### Make More Modules Build
Add stub files for missing dependencies:
```c
// modules/cmptr_accumulator/src/proof_generator.c
#include "../include/cmptr_accumulator.h"
// Add stub implementations
```

## 📋 Build Checklist

Before building:
- [ ] In project root directory?
- [ ] Submodules initialized? (`git submodule update --init`)
- [ ] Build directory clean? (`rm -rf build`)
- [ ] Using Release mode? (`-DCMAKE_BUILD_TYPE=Release`)
- [ ] Only enabling working modules?

## 🚀 Next Steps

1. **Use what works**: crypto_demo and verify_truths
2. **Fix one example**: Update SHA3 API calls
3. **Don't enable broken modules**: They're not ready
4. **Read the truth system**: Best documentation

Remember: If it's not in this guide, it probably doesn't build!