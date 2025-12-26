cmake_minimum_required(VERSION 3.10)

# BaseFold RAA Tests

# Security validation test
add_executable(basefold_raa_security_test basefold_raa_security_test.c)
target_link_libraries(basefold_raa_security_test
    PRIVATE
        basefold_raa
        sha3
        gf128
        common
        m
)
target_include_directories(basefold_raa_security_test
    PRIVATE
        ${CMAKE_SOURCE_DIR}/modules/basefold_raa/include
        ${CMAKE_SOURCE_DIR}/modules/basefold/include
        ${CMAKE_SOURCE_DIR}/modules/sha3/include
        ${CMAKE_SOURCE_DIR}/modules/gf128/include
        ${CMAKE_SOURCE_DIR}/modules/common/include
)

# Add to CTest
add_test(NAME basefold_raa_security COMMAND basefold_raa_security_test)

# Simple test (simulation)
add_executable(basefold_raa_simple_test basefold_raa_simple_test.c)
target_link_libraries(basefold_raa_simple_test 
    PRIVATE 
        common
        m
)
target_include_directories(basefold_raa_simple_test
    PRIVATE
        ${CMAKE_SOURCE_DIR}/modules/common/include
)

# Empirical test
add_executable(basefold_raa_empirical_test basefold_raa_empirical_test.c)
target_link_libraries(basefold_raa_empirical_test
    PRIVATE
        basefold_raa
        basefold
        sha3
        gf128
        common
        m
        gomp
)
target_include_directories(basefold_raa_empirical_test
    PRIVATE
        ${CMAKE_SOURCE_DIR}/modules/basefold_raa/include
        ${CMAKE_SOURCE_DIR}/modules/basefold/include
        ${CMAKE_SOURCE_DIR}/modules/sha3/include
        ${CMAKE_SOURCE_DIR}/modules/gf128/include
        ${CMAKE_SOURCE_DIR}/modules/common/include
)

# Add empirical test to CTest
add_test(NAME basefold_raa_empirical COMMAND basefold_raa_empirical_test)

# Detailed timing test
add_executable(basefold_raa_detailed_timing basefold_raa_detailed_timing.c)
target_link_libraries(basefold_raa_detailed_timing
    PRIVATE
        common
        m
)
target_include_directories(basefold_raa_detailed_timing
    PRIVATE
        ${CMAKE_SOURCE_DIR}/modules/common/include
)

# Set test properties
set_tests_properties(basefold_raa_security basefold_raa_empirical
    PROPERTIES
        TIMEOUT 60
        LABELS "security;basefold_raa"
)