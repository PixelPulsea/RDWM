#include <cerrno>
#include <iostream>
#include <string>
#include <cstdlib>

void die(const std::string& s) {
	std::cerr << s << std::endl;
	std::exit(1);
}
