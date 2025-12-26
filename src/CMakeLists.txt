# Main source CMakeLists.txt
# This handles the core library that is not part of any module

# Define the main library
add_library(gate_core
    core/gate_core.c
)

# Set include directories
target_include_directories(gate_core
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../include>
        $<INSTALL_INTERFACE:include>
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}
)

# Link with required modules
target_link_libraries(gate_core
    PUBLIC
        gate_example  # Link with gate_example module
        # Add other module dependencies here
)

# Install the library
install(TARGETS gate_core
    EXPORT GateCoreTargets
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
    RUNTIME DESTINATION bin
    INCLUDES DESTINATION include
)

# Export the targets
install(EXPORT GateCoreTargets
    FILE GateCoreTargets.cmake
    NAMESPACE GateComputer::
    DESTINATION lib/cmake/gate_core
)