#include "cpu_features.h"

bool cpu_has_pclmul(void) {
#if defined(__GNUC__) || defined(__clang__)
#if defined(__x86_64__) || defined(__i386__)
    return __builtin_cpu_supports("pclmul");
#elif defined(__aarch64__) || defined(__arm__)
    return __builtin_cpu_supports("pmull");
#else
    return false;
#endif
#else
#ifdef ENABLE_PCLMUL
    return true;
#else
    return false;
#endif
#endif
}

bool cpu_has_avx2(void) {
#if defined(__GNUC__) || defined(__clang__)
#if defined(__x86_64__) || defined(__i386__)
    return __builtin_cpu_supports("avx2") && __builtin_cpu_supports("pclmul");
#else
    return false;
#endif
#else
    return false;
#endif
}

bool cpu_has_avx512(void) {
#if defined(__GNUC__) || defined(__clang__)
#if defined(__x86_64__) || defined(__i386__)
    return __builtin_cpu_supports("avx512f") && __builtin_cpu_supports("avx512dq") && \
           __builtin_cpu_supports("avx512vl") && __builtin_cpu_supports("avx512bw") && \
           __builtin_cpu_supports("pclmul");
#else
    return false;
#endif
#else
    return false;
#endif
}