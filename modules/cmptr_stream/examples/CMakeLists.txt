# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Stream cipher demo
add_executable(cmptr_stream_demo stream_demo.c)
target_link_libraries(cmptr_stream_demo PRIVATE cmptr_stream)

# Install to bin directory
install(TARGETS cmptr_stream_demo
    RUNTIME DESTINATION bin
)