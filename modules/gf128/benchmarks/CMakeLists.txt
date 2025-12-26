cmake_minimum_required(VERSION 3.5)
project(gf128_bench C)

add_executable(bench_mul bench_mul.c)
# Link against gf128 library and pthreads for multi-threaded benchmarks
find_package(Threads REQUIRED)
target_link_libraries(bench_mul PRIVATE gf128 ${CMAKE_THREAD_LIBS_INIT})
if(USE_PCLMUL_KARATSUBA)
    target_compile_definitions(bench_mul PRIVATE USE_PCLMUL_KARATSUBA)
endif()
if(USE_AVX2)
    target_compile_definitions(bench_mul PRIVATE USE_AVX2)
endif()
if(USE_AVX512)
    target_compile_definitions(bench_mul PRIVATE USE_AVX512)
endif()
# Add experimental GFNI-only multiply flag to benchmarks
if(USE_GFNI_MUL)
    target_compile_definitions(bench_mul PRIVATE USE_GFNI_MUL)
endif()
# Propagate Karatsuba flag to benchmark executable
if(USE_PCLMUL_KARATSUBA)
    target_compile_definitions(bench_mul PRIVATE USE_PCLMUL_KARATSUBA)
endif()