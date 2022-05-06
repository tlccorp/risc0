add_executable(battleship 
	battleship.cpp
	protocol.cpp
	core.cpp
)
target_link_libraries(battleship  TBB::tbb  core zkp-prove zkp-accel-backend-cpu zkp-accel-kernels zkp-prove zkp-verify  zkvm-verify zkvm-prove zkvm-circuit zkp-core zkvm-r0vm zkvm-sdk-cpp-guest zkvm-sdk-cpp-host )

add_library(init_method init_method.cpp)
add_library(turn_method turn_method.cpp)
