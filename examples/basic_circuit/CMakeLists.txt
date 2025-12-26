cmake_minimum_required(VERSION 3.10)

# Add the example executable
add_executable(basic_circuit src/main.c)

# Link with the circuit_generator and circuit_evaluator libraries
target_link_libraries(basic_circuit PRIVATE circuit_generator circuit_evaluator)

# Set include directories
target_include_directories(basic_circuit PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src)