#include <stdio.h>
#include <stdlib.h>
#include <getopt.h>

#ifdef USE_READLINE
  // WARNING: GPL license implications
  #include <readline/readline.h>
  #include <readline/history.h>
#else
  #include <editline/readline.h>
#endif

#include "util.h"
#include "wa.h"

void usage(char *prog) {
    fprintf(stderr, "%s [--debug] WASM_FILE [--repl|-- ARG...]\n", prog);
    exit(2);
}

// Special test imports
uint32_t _spectest__global_ = 666;

void _spectest__print_(uint32_t val) {
    //printf("spectest.print 0x%x:i32\n", val);
    printf("0x%x:i32\n", val);
}


int main(int argc, char **argv) {
    char   *mod_path, *entry, *line;
    int     repl = 0, debug = 0, res = 0;

    // Parse arguments
    int option_index = 0, c;
    struct option long_options[] = {
        {"repl",  no_argument, &repl,  1},
        {"debug", no_argument, &debug, 1},
        {0,       0,           0,      0}
    };
    while ((c = getopt_long (argc, argv, "",
                             long_options, &option_index)) != -1) {
        switch (c) {
        case 0: break;
        case '?': usage(argv[0]); break;
        default: usage(argv[0]);
        }
    }
    if (optind >= argc) { usage(argv[0]); }
    mod_path = argv[optind++];

    if (debug) {
        printf("repl: %d, debug: %d, module path: %s\n",
               repl, debug, mod_path);
    }

    // Load the module
    Options opts;
    Module *m = load_module(mod_path, opts);

    if (!repl) {
        // Invoke one function and exit
        res = invoke(m, argv[optind], argc-optind-1, argv+optind+1);
        if (res) {
	    if (m->sp >= 0) {
		printf("%s\n", value_repr(&m->stack[m->sp]));
	    }
        } else {
	    error("Exception: %s\n", exception);
	    exit(1);
	}
    } else {
        // Simple REPL
        /*
        if (optind < argc) { usage(argv[0]); }
        while (line = readline("webassembly> ")) {
            int token_cnt = 0;
            char **tokens = split_string(line, &token_cnt);
            if (token_cnt == 0) { continue; }

            // Reset the stacks
            m->sp = -1;
            m->fp = -1;
            m->csp = -1;
            res = invoke(m, tokens[0], token_cnt-1, tokens+1);
	    if (res) {
		if (m->sp >= 0) {
		    printf("%s\n", value_repr(&m->stack[m->sp]));
		}
	    } else {
		error("Exception: %s\n", exception);
	    }
            free(tokens);
        }
        */
    }
    exit(0);
}
