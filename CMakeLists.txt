cmake_minimum_required(VERSION 3.16)
project(rexplus LANGUAGES CXX)

add_executable(rexplus_solver rexplus.cpp)
add_executable(rexplus_hypergraph completion_hypergraph.cpp)
add_executable(rexplus_proof_generator generate_proof.cpp)
add_executable(rexplus_proof_checker check_proof.cpp)
add_executable(rexplus_prefix_checker check_prefix.cpp)
foreach(target rexplus_solver rexplus_hypergraph rexplus_proof_generator
               rexplus_proof_checker rexplus_prefix_checker)
    target_compile_features(${target} PRIVATE cxx_std_20)
    if(MSVC)
        target_compile_options(${target} PRIVATE /O2 /W4)
    else()
        target_compile_options(${target} PRIVATE -O3 -Wall -Wextra -Wpedantic)
    endif()
endforeach()

find_package(Python3 COMPONENTS Interpreter REQUIRED)
enable_testing()
add_test(NAME small_board_equivalence
    COMMAND ${Python3_EXECUTABLE} -B ${CMAKE_CURRENT_SOURCE_DIR}/audit_hypergraph.py)
