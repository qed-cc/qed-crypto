cmake_minimum_required(VERSION 3.10)

# Add the example subdirectories only if they exist and have proper dependencies
# Commented out for now as they have missing headers
# add_subdirectory(basic_circuit)
# add_subdirectory(direct_circuit)

# Add comprehensive truth demo if truth_verifier module exists
if(TARGET truth_verifier)
    add_executable(comprehensive_truth_demo comprehensive_truth_demo.c)
    target_link_libraries(comprehensive_truth_demo PRIVATE truth_verifier)
endif()

# Add blockchain circular recursion demos if BaseFold RAA is enabled
# Commented out for now until basefold module is properly integrated
# if(BUILD_BASEFOLD_RAA)
#     # Basic blockchain demo
#     add_executable(blockchain_circular_recursion ../tools/blockchain_circular_recursion.c)
#     target_link_libraries(blockchain_circular_recursion PRIVATE 
#         basefold_raa
#         sha3
#         gf128
#         gate_core
#         m
#         ${CMAKE_THREAD_LIBS_INIT}
#     )
# endif()

# Cryptography suite overview demo (documentation only)
add_executable(crypto_demo crypto_demo.c)
# This demo is documentation-only, no libraries needed

# Compile-time proof demo
add_executable(compile_time_proof_demo compile_time_proof_demo.c)
target_include_directories(compile_time_proof_demo PRIVATE ${CMAKE_SOURCE_DIR}/include)

# New working examples with correct SHA3 API
add_executable(sha3_working sha3_working.c)
target_include_directories(sha3_working PRIVATE ${CMAKE_SOURCE_DIR}/modules/sha3/include)
target_link_libraries(sha3_working sha3)

add_executable(crypto_working crypto_working.c)
target_include_directories(crypto_working PRIVATE 
    ${CMAKE_SOURCE_DIR}/modules/sha3/include
    ${CMAKE_SOURCE_DIR}/modules/gf128/include
)
target_link_libraries(crypto_working sha3 gf128)
