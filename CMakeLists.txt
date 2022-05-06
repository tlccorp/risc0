cmake_minimum_required(VERSION 3.10)

# set the project name
project(risc0)

#set (CMAKE_CXX_FLAGS "-m32 -nostdlib")

set(CMAKE_VERBOSE_MAKEFILE ON)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED True)

find_package(TBB REQUIRED)

message(STATUS "STATUS    ////////// ${TBB_ROOT}" )

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

include_directories(${risc0_SOURCE_DIR} ${CMAKE_BINARY_DIR}  /opt/homebrew/Cellar/tbb/2021.5.0_1/include)
add_subdirectory(risc0)
add_subdirectory(examples)
