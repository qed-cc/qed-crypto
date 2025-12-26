/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef SHA3_COMPAT_H
#define SHA3_COMPAT_H

#ifdef HAS_SHA3
#include "sha3.h"
#else
/* SHA3 stub for compilation without sha3 module */
static inline void sha3_256(const uint8_t* data, size_t len, uint8_t* hash) {
    /* Simple hash stub for testing */
    for (int i = 0; i < 32; i++) {
        hash[i] = (uint8_t)(i ^ (len & 0xFF) ^ (data ? data[0] : 0));
    }
}
#endif

#endif /* SHA3_COMPAT_H */