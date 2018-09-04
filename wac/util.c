#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <math.h>
#include <limits.h>   // for CHAR_BIT
#include <string.h>
#include <sys/stat.h>
#include <fcntl.h>
//#include <sys/mman.h>

#include "util.h"

uint64_t read_LEB_(uint8_t *bytes, uint32_t *pos, uint32_t maxbits, bool sign) {
    uint64_t result = 0;
    uint32_t shift = 0;
    uint32_t bcnt = 0;
    uint32_t startpos = *pos;
    uint64_t  byte;

    while (true) {
        byte = bytes[*pos];
        *pos += 1;
        result |= ((byte & 0x7f)<<shift);
        shift += 7;
        if ((byte & 0x80) == 0) {
            break;
        }
        bcnt += 1;
        if (bcnt > (maxbits + 7 - 1) / 7) {
            FATAL("Unsigned LEB at byte %d overflow", startpos);
        }
    }
    if (sign && (shift < maxbits) && (byte & 0x40)) {
        // Sign extend
        result |= - (1 << shift);
    }
    return result;
}

uint64_t read_LEB(uint8_t *bytes, uint32_t *pos, uint32_t maxbits) {
    return read_LEB_(bytes, pos, maxbits, false);
}

uint64_t read_LEB_signed(uint8_t *bytes, uint32_t *pos, uint32_t maxbits) {
    return read_LEB_(bytes, pos, maxbits, true);
}

uint32_t read_uint32(uint8_t *bytes, uint32_t *pos) {
    *pos += 4;
    return ((uint32_t *) (bytes+*pos-4))[0];
}

// Reads a string from the bytes array at pos that starts with a LEB length
// if result_len is not NULL, then it will be set to the string length
char *read_string(uint8_t *bytes, uint32_t *pos, uint32_t *result_len) {
    uint32_t str_len = read_LEB(bytes, pos, 32);
    char * str = malloc(str_len+1);
    memcpy(str, bytes+*pos, str_len);
    str[str_len] = '\0';
    *pos += str_len;
    if (result_len) { *result_len = str_len; }
    return str;
}

// open and mmap a file
/*
uint8_t *mmap_file(char *path, uint32_t *len) {
    int          fd;
    struct stat  sb;
    uint8_t     *bytes;

    fd = open(path, O_RDONLY);
    if (fd < 0) { FATAL("could not open file '%s'\n", path); }
    if (fstat(fd, &sb) < 0) { FATAL("could stat file '%s'\n", path); }

    bytes = mmap(0, sb.st_size, PROT_READ, MAP_SHARED, fd, 0);
    if (len) {
        *len = sb.st_size;  // Return length if requested
    }
    if (bytes == MAP_FAILED) { FATAL("could not mmap file '%s'", path); }
    return bytes;
}
*/

// Assert calloc
void *acalloc(size_t nmemb, size_t size,  char *name) {
    void *res = calloc(nmemb, size);
    if (res == NULL) {
        FATAL("Could not allocate %ld bytes for %s", nmemb * size, name);
    }
    return res;
}

// Assert realloc
void *arecalloc(void *ptr, size_t old_nmemb, size_t nmemb,
                size_t size,  char *name) {
    void *res = realloc(ptr, nmemb * size);
    if (res == NULL) {
        FATAL("Could not allocate %ld bytes for %s", nmemb * size, name);
    }
    // Initialize new memory
    memset(res + old_nmemb * size, 0, (nmemb - old_nmemb) * size);
    return res;
}

// Split a space separated strings into an array of strings
// Returns 0 on failure
// Memory must be freed by caller
// Based on: http://stackoverflow.com/a/11198630/471795
char **split_string(char *str, int *count) {
    char **res = NULL;
    char  *p   = strtok(str, " ");
    int    idx = 0;

    // split string and append tokens to 'res'
    while (p) {
        res = realloc(res, sizeof(char*) * idx+1);
        if (res == NULL) {
            return 0;
        }

        res[idx++] = p;
        p = strtok(NULL, " ");
    }

    /* realloc one extra element for the last NULL */

    res = realloc (res, sizeof(char*) * (idx+1));
    res[idx] = 0;

    if (count) { *count = idx; }
    return res;
}


// Math

// Inplace sign extend
void sext_8_32(uint32_t *val) {
    if (*val & 0x80) { *val = *val | 0xffffff00; }
}
void sext_16_32(uint32_t *val) {
    if (*val & 0x8000) { *val = *val | 0xffff0000; }
}
void sext_8_64(uint64_t *val) {
    if (*val & 0x80) { *val = *val | 0xffffffffffffff00; }
}
void sext_16_64(uint64_t *val) {
    if (*val & 0x8000) { *val = *val | 0xffffffffffff0000; }
}
void sext_32_64(uint64_t *val) {
    if (*val & 0x80000000) { *val = *val | 0xffffffff00000000; }
}

// Based on: http://stackoverflow.com/a/776523/471795
uint32_t rotl32(uint32_t n, unsigned int c) {
  const unsigned int mask = (CHAR_BIT*sizeof(n)-1);
  c = c % 32;
  c &= mask;
  return (n<<c) | (n>>( (-c)&mask ));
}

uint32_t rotr32(uint32_t n, unsigned int c) {
  const unsigned int mask = (CHAR_BIT*sizeof(n)-1);
  c = c % 32;
  c &= mask;
  return (n>>c) | (n<<( (-c)&mask ));
}

uint64_t rotl64(uint64_t n, unsigned int c) {
  const unsigned int mask = (CHAR_BIT*sizeof(n)-1);
  c = c % 64;
  c &= mask;
  return (n<<c) | (n>>( (-c)&mask ));
}

uint64_t rotr64(uint64_t n, unsigned int c) {
  const unsigned int mask = (CHAR_BIT*sizeof(n)-1);
  c = c % 64;
  c &= mask;
  return (n>>c) | (n<<( (-c)&mask ));
}

double wa_fmax(double a, double b) {
    double c = fmax(a, b);
    if (c==0 && a==b) { return signbit(a) ? b : a; }
    return c;
}
double wa_fmin(double a, double b) {
    double c = fmin(a, b);
    if (c==0 && a==b) { return signbit(a) ? a : b; }
    return c;
}


// Dynamic lib resolution

// If filename is NULL, a NULL handle will be used
// Returns true if resolution successful
// Return false and sets err if resolution is not successful
/*bool resolvesym(char *filename, char *symbol, void **val, char **err) {*/
    /*void *handle = NULL;*/
    /*dlerror(); // clear errors*/
    /*if (filename) {*/
        /*handle = dlopen(filename, RTLD_LAZY);*/
        /*if (!handle) {*/
            /**err = dlerror();*/
            /*return false;*/
        /*}*/
    /*}*/
    /**val = dlsym(handle, symbol);*/
    /*if ((*err = dlerror()) != NULL) {*/
        /*return false;*/
    /*}*/
    /*return true;*/
/*}*/
