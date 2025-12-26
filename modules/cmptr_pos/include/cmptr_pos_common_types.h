/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef CMPTR_POS_COMMON_TYPES_H
#define CMPTR_POS_COMMON_TYPES_H

#include <stdint.h>
#include <stdbool.h>

/* Common hash type used across PoS modules */
typedef struct {
    uint8_t bytes[32];
} hash256_t;

/* Common signature type */
typedef struct {
    uint8_t bytes[64];
} signature_t;

/* Consensus phases */
typedef enum {
    PHASE_STAKE_SNAPSHOT = 0,
    PHASE_COMMITTEE_SELECTION = 1,
    PHASE_PROPOSAL = 2,
    PHASE_VOTING = 3,
    PHASE_COMMIT = 4,
    PHASE_FINALIZE = 5,
    PHASE_COUNT = 6
} consensus_phase_t;

/* For compatibility with existing code that uses different phase names */
#define PHASE_SNAPSHOT PHASE_STAKE_SNAPSHOT
#define PHASE_COMMITTEE PHASE_COMMITTEE_SELECTION
#define PHASE_DAG PHASE_PROPOSAL
#define PHASE_ORDERING PHASE_VOTING

/* Finality types */
typedef enum {
    FINALITY_NONE = 0,
    FINALITY_PROBABILISTIC = 1,
    FINALITY_ECONOMIC = 2,
    FINALITY_ABSOLUTE = 3
} finality_type_t;

#endif /* CMPTR_POS_COMMON_TYPES_H */