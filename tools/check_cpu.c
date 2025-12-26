/* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include "cpu_features.h"

int main() {
    printf("CPU Feature Detection:\n");
    printf("=====================\n");
    printf("AVX2:    %s\n", cpu_has_avx2() ? "YES" : "NO");
    printf("AVX512:  %s\n", cpu_has_avx512() ? "YES" : "NO");
    printf("PCLMUL:  %s\n", cpu_has_pclmul() ? "YES" : "NO");
    return 0;
}