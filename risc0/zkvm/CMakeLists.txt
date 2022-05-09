add_subdirectory(sdk)
add_subdirectory(circuit)
add_subdirectory(verify)

if(BUILD_RISCVM)
	add_subdirectory(prove)
	add_subdirectory(r0vm)
endif()
