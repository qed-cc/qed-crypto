# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Exchange demo
add_executable(cmptr_exchange_demo exchange_demo.c)
target_link_libraries(cmptr_exchange_demo PRIVATE 
    cmptr_exchange
    cmptr_channel
)

# Install to bin directory
install(TARGETS cmptr_exchange_demo
    RUNTIME DESTINATION bin
)