# SHA3 example application

add_executable(sha3_example
    src/main.c
)

# Set include directories for SHA3
target_include_directories(sha3_example
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/sha3/include
        ${CMAKE_CURRENT_SOURCE_DIR}/../../modules/common/include
)

# Link with the SHA3 library from the submodule
target_link_libraries(sha3_example
    PRIVATE
        sha3  # The submodule's library
        common
)

# Install the application
install(TARGETS sha3_example
    RUNTIME DESTINATION bin
)