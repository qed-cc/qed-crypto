/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

/* Example of how to add more truths to the system */

#include "truth_verifier.h"
#include <stdio.h>
#include <string.h>

/* Example: Verify build system uses CMake */
static truth_result_t verify_T100_uses_cmake(char *details, size_t size) {
    FILE *fp = fopen("CMakeLists.txt", "r");
    if (fp) {
        fclose(fp);
        snprintf(details, size, "Root CMakeLists.txt found");
        return TRUTH_VERIFIED;
    }
    snprintf(details, size, "No CMakeLists.txt found");
    return TRUTH_FAILED;
}

/* Example: Verify code is written in C99 */
static truth_result_t verify_T101_c99_standard(char *details, size_t size) {
    FILE *fp = fopen("CMakeLists.txt", "r");
    if (!fp) {
        snprintf(details, size, "Cannot open CMakeLists.txt");
        return TRUTH_UNCERTAIN;
    }
    
    char line[256];
    bool found = false;
    while (fgets(line, sizeof(line), fp)) {
        if (strstr(line, "CMAKE_C_STANDARD") && strstr(line, "99")) {
            found = true;
            break;
        }
    }
    fclose(fp);
    
    if (found) {
        snprintf(details, size, "C99 standard specified in CMakeLists.txt");
        return TRUTH_VERIFIED;
    }
    
    snprintf(details, size, "C standard not explicitly set to C99");
    return TRUTH_UNCERTAIN;
}

/* Example: False statement - uses Rust (should be false) */
static truth_result_t verify_F100_uses_rust(char *details, size_t size) {
    FILE *fp = fopen("Cargo.toml", "r");
    if (fp) {
        fclose(fp);
        snprintf(details, size, "Cargo.toml found - uses Rust!");
        return TRUTH_FAILED;  /* Statement should be false but is true */
    }
    
    snprintf(details, size, "No Cargo.toml - correctly not using Rust");
    return TRUTH_VERIFIED;  /* Statement is correctly false */
}

/* Example: Uncertain - performance on specific hardware */
static truth_result_t verify_U100_gpu_acceleration(char *details, size_t size) {
    snprintf(details, size, "GPU acceleration support not yet investigated");
    return TRUTH_UNCERTAIN;
}

/* Register example truths */
void register_example_truths(void) {
    static truth_statement_t example_truths[] = {
        {
            .id = "T100",
            .type = BUCKET_TRUTH,
            .statement = "Build system uses CMake",
            .category = "build",
            .verify = verify_T100_uses_cmake
        },
        {
            .id = "T101",
            .type = BUCKET_TRUTH,
            .statement = "Code is written in C99 standard",
            .category = "language",
            .verify = verify_T101_c99_standard
        },
        {
            .id = "F100",
            .type = BUCKET_FALSE,
            .statement = "Implementation uses Rust",
            .category = "language",
            .verify = verify_F100_uses_rust
        },
        {
            .id = "U100",
            .type = BUCKET_UNCERTAIN,
            .statement = "GPU acceleration is supported",
            .category = "performance",
            .verify = verify_U100_gpu_acceleration
        }
    };
    
    for (size_t i = 0; i < sizeof(example_truths) / sizeof(example_truths[0]); i++) {
        truth_verifier_register(&example_truths[i]);
    }
}