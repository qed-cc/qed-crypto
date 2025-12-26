# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# VRF demo
add_executable(cmptr_vrf_demo vrf_demo.c)
target_link_libraries(cmptr_vrf_demo PRIVATE cmptr_vrf m)

# Install to bin directory
install(TARGETS cmptr_vrf_demo
    RUNTIME DESTINATION bin
)