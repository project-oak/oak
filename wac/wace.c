#include <stdint.h>
#include <math.h>

// Call table/trapping table lookups/execution
#include <unistd.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/ucontext.h>

#include "util.h"
#include "wa.h"

void usage(char *prog) {
    fprintf(stderr, "%s [--debug] WASM_FILE [-- ARG...]\n", prog);
    exit(2);
}

/////////////////////////////////////////////////////////
// emscripten memory

#define TOTAL_MEMORY  0x1000000 // 16MB
#define TOTAL_TABLE   256

uint8_t  *_env__memory_ = 0;
uint8_t  *_env__memoryBase_;

uint32_t *_env__table_ = 0;
uint32_t *_env__tableBase_;

double    _global__NaN_         = NAN;
double    _global__Infinity_    = INFINITY;

uint32_t **_env__DYNAMICTOP_PTR_;
uint32_t *_env__tempDoublePtr_;


// Initialize memory globals and function/jump table
void emscripten_init() {
    _env__memoryBase_ = calloc(TOTAL_MEMORY, sizeof(uint8_t));

    //_env__tableBase_ = calloc(TOTAL_TABLE, sizeof(uint32_t));

    //_env__table_ = calloc(TOTAL_TABLE, sizeof(uint32_t));
    //_env__tableBase_ = 0;

    // This arrangement correlates to the module mangle_table_offset option
    if (posix_memalign((void **)&_env__table_, sysconf(_SC_PAGESIZE),
                       TOTAL_TABLE*sizeof(uint32_t))) {
        perror("posix_memalign");
        exit(1);
    }
    _env__tableBase_ = _env__table_;

    _env__tempDoublePtr_ = (uint32_t*)_env__memoryBase_;
    _env__DYNAMICTOP_PTR_ = (uint32_t**)(_env__memoryBase_ + 16);

    *_env__DYNAMICTOP_PTR_ = (uint32_t*)(_env__memoryBase_ + TOTAL_MEMORY);

    info("emscripten_init results:\n");
    info("  _env__memory_: %p (0x%x)\n", _env__memory_, _env__memory_);
    info("  _env__memoryBase_: %p\n", _env__memoryBase_);
    info("  _env__DYNAMIC_TOP_PTR_: %p\n", _env__DYNAMICTOP_PTR_);
    info("  *_env__DYNAMIC_TOP_PTR_: %p\n", *_env__DYNAMICTOP_PTR_);
    info("  _env__table_: %p\n", _env__table_);
    info("  _env__tableBase_: 0x%x\n", _env__tableBase_);


}

void segv_thunk_handler(int cause, siginfo_t * info, void *uap) {
    int index = (info->si_addr - (void *)_env__table_);
    if (info->si_addr >= (void *)_env__table_ &&
        (info->si_addr - (void *)_env__table_) < TOTAL_TABLE) {
        uint32_t fidx = _env__table_[index];
        ucontext_t *context = uap;
        void (*f)(void);
        f = setup_thunk_in(fidx);
        // Test/debug only (otherwise I/O should be avoided in a signal handlers)
        //printf("SIGSEGV raised at address %p, index: %d, fidx: %d\n",
        //        info->si_addr, index, fidx);

        // On Linux x86, general register 14 is EIP
        context->uc_mcontext.gregs[14] = (unsigned int)f;
    } else {
        // What to do here?
    }
}

void thunk_in_trap_init(Module *m) {
    // Trap on sigsegv
    struct sigaction sa;
    sa.sa_sigaction = segv_thunk_handler;
    sa.sa_flags = SA_SIGINFO;
    sigemptyset (&sa.sa_mask);
    if (sigaction (SIGSEGV, &sa, 0)) {
	perror ("sigaction");
	exit(1);
    }

    // Allow READ/WRITE but prevent execute. This only works if PROT_EXEC does
    // in fact trap
    debug("mprotect on table at: %p\n", _env__table_);
    if (mprotect(_env__table_, TOTAL_TABLE*sizeof(uint32_t),
                 PROT_READ | PROT_WRITE)) {
        perror("mprotect");
        exit(1);
    }
}


/////////////////////////////////////////////////////////
// General globals/imports

uint32_t _env__ABORT_ = 0;

#include <stdarg.h>
int _env___printf_(const char * fmt, va_list args) {
    vprintf(fmt, args);
}

void _env__abortStackOverflow_(uint32_t x) {
    FATAL("_env__abortStackOverflow 0x%x\n", x);
}

void _env__nullFunc_X_(uint32_t x) {
    FATAL("_env__nullFunc_X_ 0x%x\n", x);
}

/////////////////////////////////////////////////////////
// Command line

int main(int argc, char **argv) {
    char   *mod_path;
    int     res = 0;

    if (argc < 2) { usage(argv[0]); }
    mod_path = argv[1];

    emscripten_init();

    // Load the module
    Options opts = { .disable_memory_bounds = true,
                     .mangle_table_index    = true,
                     .dlsym_trim_underscore = true };
    Module *m = load_module(mod_path, opts);

    thunk_in_trap_init(m);

    // emscripten initialization
    res = invoke(m, "__post_instantiate", 0, 0);

    // setup argc/argv
    m->stack[++m->sp].value_type = I32;
    m->stack[m->sp].value.uint32 = argc-1;
    m->stack[++m->sp].value_type = I32;
    m->stack[m->sp].value.uint32 = (uint32_t)(argv+1);

    // Invoke main/_main function and exit
    res = invoke(m, NULL, 0, 0);

    if (!res) {
        error("Exception: %s\n", exception);
        exit(1);
    }

    if (m->sp >= 0) {
        exit(m->stack[m->sp--].value.uint32);
    } else {
        exit(0);
    }

}
