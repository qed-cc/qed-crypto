# Example application CMakeLists.txt

add_executable(simulator
    src/main.c
    # Add other source files here
)

# Link with required modules
target_link_libraries(simulator
    PRIVATE
        gate_example  # Link with gate_example module
        # Add other module dependencies here
)

# Install the application
install(TARGETS simulator
    RUNTIME DESTINATION bin
)