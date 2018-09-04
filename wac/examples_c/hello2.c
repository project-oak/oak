#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main () {
    char *name;
    name = malloc(20);
    strncpy(name, "malloc people", 14);
    printf("hello %s\n", name);
    return 2;
}
