#ifndef _filetracer_hpp_INCLUDED
#define _filetracer_hpp_INCLUDED

#include "tracer.hpp" // Alphabetically after 'filetracer'.

namespace CaDiCaL {

// File tracer class is observes proof events and additionally can be
// forced to flush or close the file.

class FileTracer : public Tracer {

public:
  FileTracer () {}
  virtual ~FileTracer () {}
  
  virtual bool closed () { return true; }
  virtual void close () {}
  virtual void flush () {}

};

} // namespace CaDiCaL

#endif
