#ifndef _features_hpp_INCLUDED
#define _features_hpp_INCLUDED

extern "C" {
#include <features.h>
};

#if _POSIX_C_SOURCE >= 1 || _XOPEN_SOURCE || _POSIX_SOURCE || _BSD_SOURCE || _SVID_SOURCE
#define HAVE_UNLOCKED_IO
#endif

#endif
