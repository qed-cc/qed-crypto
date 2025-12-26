#include <stdio.h>
#include <string.h>
#include "sha3.h"  /* Include from SHA3 submodule */
#include "logger.h"

/**
 * @brief Example application demonstrating SHA3 usage
 * @return Status code
 */
int main(int argc, char *argv[]) {
    printf("Gate Computer - SHA3 Example\n");
    printf("SHA3 library version: %s\n", sha3_version());
    
    /* Example message to hash */
    const char *message = "Hello, Gate Computer!";
    size_t msg_len = strlen(message);
    
    /* Output buffer for digest */
    uint8_t digest[SHA3_256_DIGEST_SIZE];
    
    /* Compute SHA3-256 hash */
    int result = sha3_hash(SHA3_256, message, msg_len, digest, SHA3_256_DIGEST_SIZE);
    
    if (result < 0) {
        LOG_ERROR("sha3_example", "Error computing hash");
        return 1;
    }
    
    /* Print the digest in hexadecimal */
    printf("SHA3-256 hash of \"%s\":\n", message);
    for (int i = 0; i < SHA3_256_DIGEST_SIZE; i++) {
        printf("%02x", digest[i]);
    }
    printf("\n");
    
    return 0;
}