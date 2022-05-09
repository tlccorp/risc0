if (BUILD_METHODS)
	add_subdirectory(guest)
endif()

if(BUILD_RISCVM)
	add_subdirectory(host)
endif()
