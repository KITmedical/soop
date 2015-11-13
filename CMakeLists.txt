
project(soop)

cmake_minimum_required(VERSION 2.8)

set( CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion -std=c++14" )

include_directories("include/soop")

file(GLOB lib_headers "include/soop/*.hpp")
file(GLOB lib_code    "lib/*.cpp")
file(GLOB demo_code   "demo/*.cpp")

add_library(soop ${lib_headers} ${lib_code})

add_executable(soop_demo ${demo_code})
target_link_libraries(soop_demo soop)


