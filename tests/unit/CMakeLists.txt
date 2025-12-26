# Unit tests CMakeLists.txt

# Example unit test for gate_example module
add_gate_test(test_example_unit test_example.c)
target_link_libraries(test_example_unit PRIVATE gate_example)