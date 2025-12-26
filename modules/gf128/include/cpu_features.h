#ifndef CPU_FEATURES_H
#define CPU_FEATURES_H

#include <stdbool.h>

bool cpu_has_pclmul(void);
bool cpu_has_avx2(void);
bool cpu_has_avx512(void);

#endif // CPU_FEATURES_H
