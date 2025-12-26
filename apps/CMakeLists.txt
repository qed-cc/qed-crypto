# Applications CMakeLists.txt
# This file manages all executable applications

# Function to add an application with standard configuration
function(add_gate_application APP_NAME)
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${APP_NAME}/CMakeLists.txt")
        add_subdirectory(${APP_NAME})
        message(STATUS "Added application: ${APP_NAME}")
    else()
        message(WARNING "Application directory ${APP_NAME} exists but has no CMakeLists.txt")
    endif()
endfunction()

# Add our new cmptr application explicitly
# Only build cmptr app in sandbox
add_gate_application(cmptr)
# Skip other examples (gf128_example, sha3_example, simulator)