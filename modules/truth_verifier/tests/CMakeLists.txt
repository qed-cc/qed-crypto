cmake_minimum_required(VERSION 3.10)

# Add test executable
add_executable(test_truth_verifier test_truth_verifier.c)
target_link_libraries(test_truth_verifier PRIVATE truth_verifier)

# Register test
add_test(NAME truth_verifier_test COMMAND test_truth_verifier)