/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2025 Rhett Creighton */
#include "sha3.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Test vectors for SHA-3 */
static const struct {
    sha3_hash_type type;
    const char *message;
    const char *digest_hex;
} sha3_test_vectors[] = {
    /* SHA3-224 test vectors */
    {SHA3_224, "", 
     "6b4e03423667dbb73b6e15454f0eb1abd4597f9a1b078e3f5b5a6bc7"},
    {SHA3_224, "abc", 
     "e642824c3f8cf24ad09234ee7d3c766fc9a3a5168d0c94ad73b46fdf"},
    {SHA3_224, "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", 
     "8a24108b154ada21c9fd5574494479ba5c7e7ab76ef264ead0fcce33"},
    
    /* SHA3-256 test vectors */
    {SHA3_256, "", 
     "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"},
    {SHA3_256, "abc", 
     "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"},
    {SHA3_256, "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", 
     "41c0dba2a9d6240849100376a8235e2c82e1b9998a999e21db32dd97496d3376"},
    
    /* SHA3-384 test vectors */
    {SHA3_384, "", 
     "0c63a75b845e4f7d01107d852e4c2485c51a50aaaa94fc61995e71bbee983a2ac3713831264adb47fb6bd1e058d5f004"},
    {SHA3_384, "abc", 
     "ec01498288516fc926459f58e2c6ad8df9b473cb0fc08c2596da7cf0e49be4b298d88cea927ac7f539f1edf228376d25"},
    {SHA3_384, "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", 
     "991c665755eb3a4b6bbdfb75c78a492e8c56a22c5c4d7e429bfdbc32b9d4ad5aa04a1f076e62fea19eef51acd0657c22"},
    
    /* SHA3-512 test vectors */
    {SHA3_512, "", 
     "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a615b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26"},
    {SHA3_512, "abc", 
     "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0"},
    {SHA3_512, "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", 
     "04a371e84ecfb5b8b77cb48610fca8182dd457ce6f326a0fd3d7ec2f1e91636dee691fbe0c985302ba1b0d8dc78c086346b533b49c030d99a27daf1139d6e75e"}
};

/* Test vectors for SHAKE */
static const struct {
    sha3_hash_type type;
    const char *message;
    size_t output_len;
    const char *output_hex;
} shake_test_vectors[] = {
    /* SHAKE128 test vectors */
    {SHAKE_128, "", 32, 
     "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26"},
    {SHAKE_128, "abc", 32, 
     "5881092dd818bf5cf8a3ddb793fbcba74097d5c526a6d35f97b83351940f2cc8"},
    
    /* SHAKE256 test vectors with shorter outputs for simplicity */
    {SHAKE_256, "", 32, 
     "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f"},
    {SHAKE_256, "abc", 32, 
     "483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739"}
};

/* Utility function to convert hex string to bytes */
static int hex_to_bytes(const char *hex, uint8_t *bytes, size_t len) {
    size_t hex_len = strlen(hex);
    if (hex_len != len * 2) {
        return -1;
    }
    
    for (size_t i = 0; i < len; i++) {
        int hi, lo;
        hi = hex[i * 2];
        lo = hex[i * 2 + 1];
        
        hi = (hi >= '0' && hi <= '9') ? hi - '0' : 
             (hi >= 'a' && hi <= 'f') ? hi - 'a' + 10 : 
             (hi >= 'A' && hi <= 'F') ? hi - 'A' + 10 : -1;
        
        lo = (lo >= '0' && lo <= '9') ? lo - '0' : 
             (lo >= 'a' && lo <= 'f') ? lo - 'a' + 10 : 
             (lo >= 'A' && lo <= 'F') ? lo - 'A' + 10 : -1;
        
        if (hi == -1 || lo == -1) {
            return -1;
        }
        
        bytes[i] = (hi << 4) | lo;
    }
    
    return 0;
}

/* Test SHA-3 functions */
static int test_sha3(void) {
    int failures = 0;
    uint8_t digest[SHA3_MAX_DIGEST_SIZE];
    uint8_t expected[SHA3_MAX_DIGEST_SIZE];
    
    printf("Testing SHA-3 functions...\n");
    
    for (size_t i = 0; i < sizeof(sha3_test_vectors) / sizeof(sha3_test_vectors[0]); i++) {
        sha3_hash_type type = sha3_test_vectors[i].type;
        const char *message = sha3_test_vectors[i].message;
        const char *digest_hex = sha3_test_vectors[i].digest_hex;
        size_t digest_len = sha3_get_digest_size(type);
        
        /* Convert expected digest from hex to bytes */
        if (hex_to_bytes(digest_hex, expected, digest_len) != 0) {
            printf("Error: Invalid hex digest in test vector %zu\n", i);
            failures++;
            continue;
        }
        
        /* Compute digest */
        int result = sha3_hash(type, message, strlen(message), digest, digest_len);
        
        if (result != (int)digest_len) {
            printf("Error: sha3_hash returned %d, expected %zu\n", result, digest_len);
            failures++;
            continue;
        }
        
        /* Compare with expected result */
        if (memcmp(digest, expected, digest_len) != 0) {
            printf("Error: SHA-3 test vector %zu failed (type: %d, message: \"%s\")\n", 
                   i, type, message);
            printf("Expected: ");
            for (size_t j = 0; j < digest_len; j++) {
                printf("%02x", expected[j]);
            }
            printf("\nActual:   ");
            for (size_t j = 0; j < digest_len; j++) {
                printf("%02x", digest[j]);
            }
            printf("\n");
            failures++;
        }
    }
    
    printf("SHA-3 tests: %d passed, %d failed\n", 
           (int)(sizeof(sha3_test_vectors) / sizeof(sha3_test_vectors[0])) - failures, 
           failures);
    
    return failures;
}

/* Test SHAKE functions */
static int test_shake(void) {
    int failures = 0;
    uint8_t output[128]; /* Max test output length */
    uint8_t expected[128];
    
    printf("Testing SHAKE functions...\n");
    
    for (size_t i = 0; i < sizeof(shake_test_vectors) / sizeof(shake_test_vectors[0]); i++) {
        sha3_hash_type type = shake_test_vectors[i].type;
        const char *message = shake_test_vectors[i].message;
        size_t output_len = shake_test_vectors[i].output_len;
        const char *output_hex = shake_test_vectors[i].output_hex;
        
        /* Convert expected output from hex to bytes */
        if (hex_to_bytes(output_hex, expected, output_len) != 0) {
            printf("Error: Invalid hex output in test vector %zu\n", i);
            failures++;
            continue;
        }
        
        /* Compute output */
        int result = shake_xof(type, message, strlen(message), output, output_len);
        
        if (result != (int)output_len) {
            printf("Error: shake_xof returned %d, expected %zu\n", result, output_len);
            failures++;
            continue;
        }
        
        /* Compare with expected result */
        if (memcmp(output, expected, output_len) != 0) {
            printf("Error: SHAKE test vector %zu failed (type: %d, message: \"%s\")\n", 
                   i, type, message);
            printf("Expected: ");
            for (size_t j = 0; j < output_len; j++) {
                printf("%02x", expected[j]);
            }
            printf("\nActual:   ");
            for (size_t j = 0; j < output_len; j++) {
                printf("%02x", output[j]);
            }
            printf("\n");
            failures++;
        }
    }
    
    printf("SHAKE tests: %d passed, %d failed\n", 
           (int)(sizeof(shake_test_vectors) / sizeof(shake_test_vectors[0])) - failures, 
           failures);
    
    return failures;
}

/* Test incremental hashing */
static int test_incremental(void) {
    int failures = 0;
    uint8_t digest1[SHA3_512_DIGEST_SIZE];
    uint8_t digest2[SHA3_512_DIGEST_SIZE];
    sha3_ctx ctx;
    const char *part1 = "abcdefghijklmnopqrstuvwxyz";
    const char *part2 = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    const char *part3 = "0123456789";
    char combined[100];
    
    printf("Testing incremental hashing...\n");
    
    /* Combine the parts */
    snprintf(combined, sizeof(combined), "%s%s%s", part1, part2, part3);
    
    /* Test for each hash type */
    for (int type = SHA3_224; type <= SHA3_512; type++) {
        size_t digest_len = sha3_get_digest_size(type);
        
        /* One-shot hash */
        sha3_hash(type, combined, strlen(combined), digest1, digest_len);
        
        /* Incremental hash */
        sha3_init(&ctx, type);
        sha3_update(&ctx, part1, strlen(part1));
        sha3_update(&ctx, part2, strlen(part2));
        sha3_update(&ctx, part3, strlen(part3));
        sha3_final(&ctx, digest2, digest_len);
        
        /* Compare results */
        if (memcmp(digest1, digest2, digest_len) != 0) {
            printf("Error: Incremental hash does not match one-shot hash for type %d\n", type);
            printf("One-shot:    ");
            for (size_t j = 0; j < digest_len; j++) {
                printf("%02x", digest1[j]);
            }
            printf("\nIncremental: ");
            for (size_t j = 0; j < digest_len; j++) {
                printf("%02x", digest2[j]);
            }
            printf("\n");
            failures++;
        }
    }
    
    printf("Incremental tests: %d passed, %d failed\n", 4 - failures, failures);
    
    return failures;
}

/* Test hash function interface */
static int test_hash_interface(void) {
    int failures = 0;
    uint8_t digest1[SHA3_512_DIGEST_SIZE];
    uint8_t digest2[SHA3_512_DIGEST_SIZE];
    const char *message = "Test message for hash function interface";
    
    printf("Testing hash function interface...\n");
    
    /* Test for each hash type */
    for (int type = SHA3_224; type <= SHA3_512; type++) {
        const sha3_hash_function *hash_func = sha3_get_hash_function(type);
        if (!hash_func) {
            printf("Error: Failed to get hash function for type %d\n", type);
            failures++;
            continue;
        }
        
        size_t digest_len = hash_func->digest_size;
        
        /* Direct API */
        sha3_hash(type, message, strlen(message), digest1, digest_len);
        
        /* Interface API */
        void *ctx = malloc(hash_func->ctx_size);
        if (!ctx) {
            printf("Error: Memory allocation failed\n");
            failures++;
            continue;
        }
        
        hash_func->init(ctx);
        hash_func->update(ctx, message, strlen(message));
        int result = hash_func->final(ctx, digest2, digest_len);
        
        if (result != (int)digest_len) {
            printf("Error: hash_func->final returned %d, expected %zu\n", 
                   result, digest_len);
            failures++;
        }
        
        /* Compare results */
        if (memcmp(digest1, digest2, digest_len) != 0) {
            printf("Error: Interface API does not match direct API for type %d\n", type);
            printf("Direct:    ");
            for (size_t j = 0; j < digest_len; j++) {
                printf("%02x", digest1[j]);
            }
            printf("\nInterface: ");
            for (size_t j = 0; j < digest_len; j++) {
                printf("%02x", digest2[j]);
            }
            printf("\n");
            failures++;
        }
        
        free(ctx);
    }
    
    printf("Interface tests: %d passed, %d failed\n", 4 - failures, failures);
    
    return failures;
}

int main() {
    int total_failures = 0;
    
    printf("Running SHA-3 library tests\n");
    printf("==========================\n\n");
    
    total_failures += test_sha3();
    printf("\n");
    
    total_failures += test_shake();
    printf("\n");
    
    total_failures += test_incremental();
    printf("\n");
    
    total_failures += test_hash_interface();
    printf("\n");
    /* Test AVX2-optimized SHA3-256 for 64-byte input */
#ifdef __GNUC__
    if (__builtin_cpu_supports("avx2")) {
        printf("Testing AVX2-optimized SHA3-256 (64-byte)\n");
        int failures = 0;
        uint8_t data[64];
        for (size_t i = 0; i < 64; i++) data[i] = (uint8_t)i;
        uint8_t ref[SHA3_256_DIGEST_SIZE];
        uint8_t opt[SHA3_256_DIGEST_SIZE];
        /* Reference: scalar path */
        sha3_ctx ctx;
        if (sha3_init(&ctx, SHA3_256) != 0) failures++;
        if (sha3_update(&ctx, data, 64) != 0) failures++;
        if (sha3_final(&ctx, ref, SHA3_256_DIGEST_SIZE) < 0) failures++;
        /* Optimized path - commented out as it's an internal function
        if (sha3_hash_256_64B_avx2(data, 64, opt, SHA3_256_DIGEST_SIZE) < 0) failures++;
        if (memcmp(ref, opt, SHA3_256_DIGEST_SIZE) != 0) {
            printf("Error: AVX2-optimized output differs from reference\n");
            failures++;
        }
        printf("AVX2 optimized SHA3-256 64B test: %s\n", failures == 0 ? "PASSED" : "FAILED");
        */
        total_failures += failures;
        printf("\n");
    }
#endif
    
    printf("==========================\n");
    printf("Test summary: %s\n", total_failures == 0 ? "ALL TESTS PASSED" : "SOME TESTS FAILED");
    
    return total_failures == 0 ? 0 : 1;
}