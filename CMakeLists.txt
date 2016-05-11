
project(soop)

cmake_minimum_required(VERSION 2.8)

set( CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion -std=c++14" )

include_directories("include")


file(GLOB lib_headers   "include/soop/*.hpp")
file(GLOB lib_code      "lib/*.cpp")
file(GLOB demo_headers  "demo/src/*.hpp")
file(GLOB demo_code     "demo/src/*.cpp")
file(GLOB demo2_headers "demo2/src/*.hpp")
file(GLOB demo2_code    "demo2/src/*.cpp")
file(GLOB demo3_headers "demo3/src/*.hpp")
file(GLOB demo3_code    "demo3/src/*.cpp")
file(GLOB test_code     "test/*.cpp")

add_library(soop ${lib_headers} ${lib_code})

add_executable(soop_demo ${demo_code} ${demo_headers})
target_link_libraries(soop_demo soop)

add_executable(soop_demo2 ${demo2_code} ${demo2_headers})
target_link_libraries(soop_demo2 soop)

add_executable(soop_demo3 ${demo3_code} ${demo3_headers})
target_link_libraries(soop_demo3 soop)

add_executable(soop_test ${test_code})
target_link_libraries(soop_test soop)
add_test(NAME soop-test COMMAND soop_test)
enable_testing(true)

