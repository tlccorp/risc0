
if (WIN32)
	set (PLATFORM_RNG rng_win32.cpp)
        #rng_linux.cpp rng_macos.cpp rng_win32.cpp
endif (WIN32)

if (APPLE)
        set (PLATFORM_RNG rng_macos.cpp)
endif (APPLE)

if (LINUX)
        set (PLATFORM_RNG rng_macos.cpp)
endif (LINUX)


set (CPU_SOURCES elf.cpp  rng.cpp)
if(BUILD_EOS)
  set (CPU_SOURCES )
endif()

add_library(core 
	log.cpp  
	${CPU_SOURCES}
        ${PLATFORM_RNG}
)
