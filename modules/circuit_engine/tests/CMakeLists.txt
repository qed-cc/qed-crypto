cmake_minimum_required(VERSION 3.10)

# Add test target
add_executable(test_circuit_engine
    test_circuit_engine.c
)

# Include directories
target_include_directories(test_circuit_engine
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/../include
        ${CMAKE_CURRENT_SOURCE_DIR}/../src
)

# Link dependencies
target_link_libraries(test_circuit_engine
    PRIVATE
        circuit_engine
)

# Add test
add_test(
    NAME test_circuit_engine
    COMMAND test_circuit_engine
)