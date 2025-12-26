cmake_minimum_required(VERSION 3.10)

# Enable testing
enable_testing()

# Round-trip test
add_executable(enc_roundtrip enc_roundtrip.c)
target_link_libraries(enc_roundtrip basefold)
add_test(NAME enc_roundtrip COMMAND enc_roundtrip)

# Full-size test  
add_executable(enc_size enc_size.c)
target_link_libraries(enc_size basefold)
add_test(NAME enc_size COMMAND enc_size)

# Set test properties
set_tests_properties(enc_roundtrip PROPERTIES TIMEOUT 30)
set_tests_properties(enc_size PROPERTIES TIMEOUT 120)

# Sumcheck benchmark
add_executable(benchmark_sumcheck benchmark_sumcheck.c)
target_link_libraries(benchmark_sumcheck basefold)