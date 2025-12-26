cmake_minimum_required(VERSION 3.5)
project(gf128_examples C)

add_executable(example example.c)
target_link_libraries(example PRIVATE gf128)