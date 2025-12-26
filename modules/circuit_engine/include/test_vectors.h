#ifndef TEST_VECTORS_H
#define TEST_VECTORS_H

/**
 * @file test_vectors.h
 * @brief Official NIST test vectors for SHA3 validation
 * 
 * This file contains test vectors for validating SHA3 implementations
 * from the NIST SHA-3 validation system.
 */

#include <stdint.h>

// SHA3-256 test vectors with input and expected output
typedef struct {
    const char *input;      // Input string
    const char *input_hex;  // Input in hex format (for non-printable inputs)
    const char *output_hex; // Expected output in hex format
} sha3_test_vector_t;

// Standard test vectors for SHA3-256
static const sha3_test_vector_t SHA3_256_VECTORS[] = {
    // Empty string
    {
        "",
        "",
        "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
    },
    // "abc" string
    {
        "abc",
        "616263",
        "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
    },
    // NIST standard test vector
    {
        "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
        "6162636462636465636465666465666765666768666768696768696a68696a6b696a6b6c6a6b6c6d6b6c6d6e6c6d6e6f6d6e6f706e6f7071",
        "41c0dba2a9d6240849100376a8235e2c82e1b9998a999e21db32dd97496d3376"
    },
    // NIST standard million-a test vector
    {
        // This is just the marker, the actual test builds the string dynamically
        "MILLION_A",
        "MILLION_A_HEX",
        "5c8875ae474a3634ba4fd55ec85bffd661f32aca75c6d699d0cdcb6c115891c1"
    }
};

// Standard test vectors for SHA3-512
static const sha3_test_vector_t SHA3_512_VECTORS[] = {
    // Empty string
    {
        "",
        "",
        "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a615b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26"
    },
    // "abc" string
    {
        "abc",
        "616263",
        "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0"
    },
    // NIST standard test vector
    {
        "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
        "6162636462636465636465666465666765666768666768696768696a68696a6b696a6b6c6a6b6c6d6b6c6d6e6c6d6e6f6d6e6f706e6f7071",
        "04a371e84ecfb5b8b77cb48610fca8182dd457ce6f326a0fd3d7ec2f1e91636dee691fbe0c985302ba1b0d8dc78c086346b533b49c030d99a27daf1139d6e75e"
    },
    // NIST standard million-a test vector
    {
        // This is just the marker, the actual test builds the string dynamically
        "MILLION_A",
        "MILLION_A_HEX",
        "3c3a876da14034ab60627c077bb98f7e120a2a5370212dffb3385a18d4f38859ed311d0a9d5141ce9cc5c66ee689b266a8aa18ace8282a0e0db596c90b0a7b87"
    }
};

#endif /* TEST_VECTORS_H */