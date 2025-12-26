# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Channel demo
add_executable(cmptr_channel_demo channel_demo.c)
target_link_libraries(cmptr_channel_demo PRIVATE cmptr_channel)

# Install to bin directory
install(TARGETS cmptr_channel_demo
    RUNTIME DESTINATION bin
)