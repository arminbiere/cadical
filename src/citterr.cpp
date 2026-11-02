#include <new>

extern "C" {
void kitten_error (const char *, ...) { throw std::bad_alloc (); }
}
