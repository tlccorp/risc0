if(BUILD_RISCVM)
	add_subdirectory(core)
	add_subdirectory(prove)
	add_subdirectory(accel)
endif()

if (BUILD_HOST_VERIFY)
	add_subdirectory(verify)
endif()
