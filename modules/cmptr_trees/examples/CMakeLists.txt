# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Trees demo
add_executable(cmptr_trees_demo trees_demo.c)
target_link_libraries(cmptr_trees_demo PRIVATE cmptr_trees m)

# Install to bin directory
install(TARGETS cmptr_trees_demo
    RUNTIME DESTINATION bin
)