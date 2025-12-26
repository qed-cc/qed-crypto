# GF128 example application

add_executable(gf128_example
    src/main.c
)

# Set include directories for GF128
target_include_directories(gf128_example
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/gf128/include
)

# Link with the GF128 library from the submodule
target_link_libraries(gf128_example
    PRIVATE
        gf128  # The submodule's library
)

# Install the application
install(TARGETS gf128_example
    RUNTIME DESTINATION bin
)