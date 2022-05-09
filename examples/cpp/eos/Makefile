everify.wasm: everify.cpp everify.hpp
	eosio-cpp  -abigen everify.cpp  rx/merkle.cpp rx/taps.cpp rx/verify.cpp rx/fri.cpp  -std=c++17 rx/ntt.cpp rx/poly.cpp rx/sha_rng.cpp -I./rx  -I./ -o  ./everify.wasm
clean:
	rm -f *.wasm *.abi *.orig

style:
	astyle --style=kr --add-braces --indent=tab decentworlds.hpp
	astyle --style=kr --add-braces --indent=tab decentworlds.cpp
