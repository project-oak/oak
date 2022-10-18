#if !defined(TF_LITE_STRIP_ERROR_STRINGS)
void MicroPrintf(const char* format, ...);
#else
#define MicroPrintf(...)
#endif

extern "C" {
int* __errno_location() {
  // Oak supports only single-threading for now hence
  // a singleton errno instance is used. 
  static int errno = 0;
  return &errno;
}

void __assert_fail(
    const char* assertion,
    const char* file,
    unsigned int line,
    const char* function) {
  // Pipe to Oak debug log channel.
  MicroPrintf("%s in %s:%d %s", assertion, file, line, function);
}

int atexit(void (*)()) {
  // *NOT* used when linking to Oak Kernel/Runtime since
  // this function is simply used to build a self-contained
  // program binary to run and debug models locally.
  return 0;
}

void abort() {
  // TODO: trigger a panic or VM shutdown
  MicroPrintf("Aborting...");

  // abort is a 'noreturn' function.
  while (1);
}
}
