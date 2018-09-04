#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>

#include <editline/readline.h>

int main()
{
    char *ast, *exp;
    char prompt[100];

    // Set the initial prompt
    snprintf(prompt, sizeof(prompt), "echo> ");
 
    for(;;) {
        char *line;
        line = readline(prompt);
        if (!line) return 0; // EOF
        add_history(line); // Add input to history.

        printf("line: %s\n", line);
    }
}
