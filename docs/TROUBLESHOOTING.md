# 🔧 CMPTR Troubleshooting Guide

## 🚨 Build Errors

### Error: "sha3_init: undefined reference"
```
undefined reference to `sha3_init'
undefined reference to `sha3_update'
undefined reference to `sha3_final'
```

**Cause**: Code uses old SHA3 API that no longer exists

**Solution**: Update to new API:
```c
// OLD (broken):
sha3_ctx ctx;
sha3_init(&ctx, 32);
sha3_update(&ctx, data, len);
sha3_final(hash, &ctx);

// NEW (working):
#include "sha3.h"
uint8_t hash[32];
sha3_hash(SHA3_256, data, len, hash, sizeof(hash));
```

### Error: "proof_generator.c: No such file"
```
CMake Error: Cannot find source file:
  modules/cmptr_accumulator/src/proof_generator.c
```

**Cause**: File referenced in CMakeLists.txt doesn't exist

**Quick Fix**:
```bash
touch modules/cmptr_accumulator/src/proof_generator.c
```

**Proper Fix**: Remove from CMakeLists.txt or implement the module

### Error: "SHA3_256 undeclared"
```
error: 'SHA3_256' undeclared (first use in this function)
```

**Cause**: Missing include or wrong constant name

**Solution**:
```c
#include "sha3.h"  // Add this
// SHA3_256 is defined in sha3.h
```

### Error: Build fails with many undefined references
**Solution**: Use the working build configuration:
```bash
./BUILD_WORKING_CONFIG.sh
```
This only builds modules that actually work.

## 🐛 Runtime Errors

### Problem: Segmentation fault in SHA3
**Cause**: Usually passing wrong size to sha3_hash()

**Fix**:
```c
// WRONG:
sha3_hash(SHA3_256, data, len, hash, 64);  // SHA3-256 is 32 bytes!

// RIGHT:
sha3_hash(SHA3_256, data, len, hash, 32);  // Correct size
```

### Problem: "Assertion failed: enable_zk == 1"
**Cause**: Trying to disable zero-knowledge (violates Axiom A002)

**Fix**: Zero-knowledge is mandatory. Always use:
```c
params.enable_zk = 1;  // Required by axiom
```

### Problem: Proof verification fails
**Common Causes**:
1. Mismatched parameters between prover and verifier
2. Corrupted proof data
3. Wrong field size (must use GF(2^128))

**Debug Steps**:
```bash
# Run with verbose output
./build/bin/verify_truths -v

# Check specific truth
./build/bin/verify_truths --id T004
```

## 🔨 CMake Issues

### Problem: "Unknown CMake command: add_module"
**Cause**: Not including the CMake helper

**Fix**: Add to your CMakeLists.txt:
```cmake
include(${CMAKE_SOURCE_DIR}/cmake/AddModule.cmake)
```

### Problem: Submodule errors
```
fatal: No url found for submodule path 'modules/sha3'
```

**Fix**:
```bash
git submodule update --init --recursive
```

### Problem: Can't find headers
**Fix**: Add include directories:
```cmake
target_include_directories(mytarget PRIVATE
    ${CMAKE_SOURCE_DIR}/modules/sha3/include
    ${CMAKE_SOURCE_DIR}/modules/gf128/include
)
```

## 🔍 Debugging Tips

### Enable Debug Build
```bash
mkdir build-debug && cd build-debug
cmake -DCMAKE_BUILD_TYPE=Debug ..
make -j$(nproc)

# Now you can use gdb
gdb ./bin/my_program
```

### Check Truth System
The truth system documents what should work:
```bash
# List all truths
./build/bin/verify_truths --list | grep "^T" | head -20

# See what's verified vs WIP
./build/bin/verify_truths --summary
```

### Find Working Examples
```bash
# See what actually builds
find build/bin -type f -executable

# Working demos:
./build/bin/crypto_demo
./build/bin/compile_time_proof_demo
./build/bin/verify_truths
```

## 📋 Common Misconceptions

### "Why not 128-bit security?"
**Answer**: Limited by GF(2^128) field and sumcheck protocol. 121 bits is the theoretical maximum. See truth T004.

### "Why can't I use SHA2/Blake3?"
**Answer**: Axiom A001 - Only SHA3 is allowed. This is a fundamental design decision for security analysis.

### "Why is zero-knowledge mandatory?"
**Answer**: Axiom A002 - Privacy is not optional. The overhead is <1% so there's no reason to disable it.

### "Why does it need AVX-512?"
**Answer**: For performance targets (150ms proofs). Code works without it but slower (~3.7 seconds).

## 🆘 Getting Help

### Before Asking for Help

1. **Check the build**: `./BUILD_WORKING_CONFIG.sh`
2. **Read the truths**: `./build/bin/verify_truths --list | grep -i yourtopic`
3. **Search existing issues**: GitHub issues may have your answer
4. **Try the working demos**: They show correct API usage

### Information to Provide

When filing an issue, include:
```bash
# System info
uname -a
gcc --version
cmake --version

# Build output
./BUILD_WORKING_CONFIG.sh 2>&1 | tee build.log

# Specific error
# Copy the FULL error message, not just one line
```

### Quick Fixes to Try

1. **Clean rebuild**:
   ```bash
   rm -rf build
   ./BUILD_WORKING_CONFIG.sh
   ```

2. **Update submodules**:
   ```bash
   git submodule update --init --recursive
   ```

3. **Check API version**:
   ```bash
   grep -r "sha3_init\|sha3_update\|sha3_final" examples/
   # These are OLD API - need updating
   ```

4. **Use working examples as reference**:
   ```bash
   less examples/crypto_working.c
   # This has correct API usage
   ```

## 🎯 Prevention

### Always Test Changes
```bash
# After any code change:
./build/bin/verify_truths        # Still works?
./build/bin/compile_time_proof_demo  # Axioms intact?
```

### Follow the Patterns
- Look at `examples/crypto_working.c` for correct API usage
- Check `include/compile_time_proofs.h` for constants
- Read module README files before using them

### Document Issues
If you solve a problem, add it here! Future developers will thank you.

## 🚀 Pro Tips

1. **Truth system is your friend** - It documents what actually works
2. **Start with working demos** - They have correct API usage  
3. **Compile-time proofs catch errors** - If it compiles, axioms are satisfied
4. **Small changes** - Test after each change to isolate issues
5. **Read the headers** - `modules/*/include/*.h` has the real API

Remember: Most "bugs" are just outdated API usage. The core system works!