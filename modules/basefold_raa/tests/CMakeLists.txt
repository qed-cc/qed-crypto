# BaseFold RAA tests

# Main test executable
add_executable(test_basefold_raa test_basefold_raa.c)
target_link_libraries(test_basefold_raa 
    basefold_raa
    gf128
    sha3
    basefold
    common
    m
)

# Add test
add_test(NAME basefold_raa_test COMMAND test_basefold_raa)

# Enable testing features
target_compile_definitions(test_basefold_raa PRIVATE TESTING)