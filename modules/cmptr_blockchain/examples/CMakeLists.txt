# SPDX-FileCopyrightText: 2025 Rhett Creighton
# SPDX-License-Identifier: Apache-2.0

# Blockchain network simulation
add_executable(blockchain_demo blockchain_demo.c)
target_link_libraries(blockchain_demo cmptr_blockchain cmptr_accumulator pthread)

# Validator node demo
add_executable(validator_demo validator_demo.c)
target_link_libraries(validator_demo cmptr_blockchain pthread)