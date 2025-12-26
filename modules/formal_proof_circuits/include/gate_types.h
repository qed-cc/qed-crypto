/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0 */

#ifndef GATE_TYPES_H
#define GATE_TYPES_H

// Gate types used in circuit compilation
typedef enum {
    GATE_AND = 0,
    GATE_OR = 1,
    GATE_NOT = 2,
    GATE_XOR = 3,
    GATE_IMPLIES = 4,
    GATE_IFF = 5,
    GATE_FORALL = 6,
    GATE_EXISTS = 7
} gate_type_t;

#endif // GATE_TYPES_H