
project(soop)

cmake_minimum_required(VERSION 2.8)

set( CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion -std=c++14" )

file(GLOB source_files "src/*.cpp")
file(GLOB header_files "src/*.hpp")

add_executable(soop ${source_files} ${header_files})


