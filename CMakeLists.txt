cmake_minimum_required(VERSION 3.0)
project(Cadical C CXX)

enable_testing()

set(VERSION "0.0")
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/config.hpp.in ${CMAKE_CURRENT_BINARY_DIR}/config.hpp)
include_directories(${CMAKE_CURRENT_BINARY_DIR})

include_directories(${CMAKE_CURRENT_SOURCE_DIR}/src)

add_subdirectory(src)
add_subdirectory(test)
