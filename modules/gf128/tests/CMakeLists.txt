cmake_minimum_required(VERSION 3.5)
project(gf128_tests C)

add_executable(test_gf128 test_gf128.c)
target_link_libraries(test_gf128 PRIVATE gf128)
add_test(NAME test_gf128 COMMAND test_gf128)

# Benchmark target for GF128 multiply variants
add_executable(bench_gf128 bench_gf128.c)
target_link_libraries(bench_gf128 PRIVATE gf128)
target_compile_definitions(bench_gf128 PRIVATE USE_AVX2 USE_AVX512)
add_test(NAME bench_gf128 COMMAND bench_gf128)