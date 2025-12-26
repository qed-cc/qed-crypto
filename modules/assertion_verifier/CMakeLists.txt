cmake_minimum_required(VERSION 3.10)
project(assertion_verifier C)

# C99 standard
set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)

# Library
add_library(assertion_verifier STATIC
    src/assertion_chain.c
    src/fopl_verifier.c
    src/ai_consensus.c
    src/sha3_validity.c
)

# Include directories
target_include_directories(assertion_verifier
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:include>
    PRIVATE
        ${CMAKE_SOURCE_DIR}/modules/sha3/include
)

# Link dependencies
target_link_libraries(assertion_verifier
    PUBLIC
        sha3
        gf128
)

# Executable for testing
add_executable(verify_assertions src/main.c)
target_link_libraries(verify_assertions PRIVATE assertion_verifier)

# Installation
install(TARGETS assertion_verifier verify_assertions
    EXPORT assertion_verifierTargets
    RUNTIME DESTINATION bin
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
)

install(DIRECTORY include/
    DESTINATION include
)

# Export targets
install(EXPORT assertion_verifierTargets
    FILE assertion_verifierTargets.cmake
    NAMESPACE assertion_verifier::
    DESTINATION lib/cmake/assertion_verifier
)

# Config file
configure_file(cmake/assertion_verifierConfig.cmake.in
    "${CMAKE_CURRENT_BINARY_DIR}/assertion_verifierConfig.cmake"
    @ONLY
)

install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/assertion_verifierConfig.cmake"
    DESTINATION lib/cmake/assertion_verifier
)