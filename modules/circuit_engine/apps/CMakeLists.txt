cmake_minimum_required(VERSION 3.10)

# Add the circuit engine app
add_executable(circuit_engine_app 
    ${CMAKE_CURRENT_SOURCE_DIR}/../src/main.c
)

# Include directories
target_include_directories(circuit_engine_app PRIVATE 
    ${CMAKE_CURRENT_SOURCE_DIR}/../include
    ${CMAKE_CURRENT_SOURCE_DIR}/../src
)

# Link to the main library
target_link_libraries(circuit_engine_app
    PRIVATE
        circuit_engine
)

# Add the final SHA3 implementation test (disabled - file doesn't exist)
# add_executable(circuit_engine_test
#     ${CMAKE_CURRENT_SOURCE_DIR}/../../gate_computer/final_sha3_impl_test.c
# )

# Include directories for the test
# target_include_directories(circuit_engine_test PRIVATE
#     ${CMAKE_CURRENT_SOURCE_DIR}/../include
#     ${CMAKE_CURRENT_SOURCE_DIR}/../src
# )

# Link the test to the main library
# target_link_libraries(circuit_engine_test
#     PRIVATE
#         circuit_engine
# )

# Install the executables
install(TARGETS
    circuit_engine_app
    DESTINATION bin
)