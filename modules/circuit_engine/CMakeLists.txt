cmake_minimum_required(VERSION 3.10)
project(circuit_engine C)

# Create library target
add_library(circuit_engine
    src/sha3_final.c
    src/circuit_format.c
    src/evaluator.c
)

# Include directories
target_include_directories(circuit_engine
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/src
)

# Dependencies (commented out - these modules don't exist as packages)
# find_package(circuit_io REQUIRED)
# find_package(circuit_evaluator REQUIRED)

# Link dependencies (use internal includes only)
# target_link_libraries(circuit_engine
#     PUBLIC
#         circuit_io
#         circuit_evaluator
# )

# Set compile definitions
target_compile_definitions(circuit_engine PRIVATE CIRCUIT_IO_HAVE_PARSE_FILE)

# Generate and install export targets
include(CMakePackageConfigHelpers)
include(GNUInstallDirs)

# Export targets
install(TARGETS circuit_engine
    EXPORT circuit_engineTargets
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
    RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
)

# Install header files
install(FILES include/circuit_engine.h
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)

# Install export targets
install(EXPORT circuit_engineTargets
    FILE circuit_engineTargets.cmake
    NAMESPACE circuit_engine::
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/circuit_engine
)

# Generate package config file
configure_package_config_file(
    ${CMAKE_CURRENT_SOURCE_DIR}/cmake/circuit_engineConfig.cmake.in
    ${CMAKE_CURRENT_BINARY_DIR}/circuit_engineConfig.cmake
    INSTALL_DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/circuit_engine
)

# Generate package version file
write_basic_package_version_file(
    ${CMAKE_CURRENT_BINARY_DIR}/circuit_engineConfigVersion.cmake
    VERSION 1.0.0
    COMPATIBILITY SameMajorVersion
)

# Install package config files
install(FILES
    ${CMAKE_CURRENT_BINARY_DIR}/circuit_engineConfig.cmake
    ${CMAKE_CURRENT_BINARY_DIR}/circuit_engineConfigVersion.cmake
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/circuit_engine
)

# Add tests subdirectory if present
if(EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/tests)
    add_subdirectory(tests)
endif()

# Add apps subdirectory
add_subdirectory(apps EXCLUDE_FROM_ALL)