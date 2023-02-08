multilibtool_LIBRARIES += %D%/liboak.a
%C%_liboak_a_CPPFLAGS = -I$(srcdir)/%D%
%C%_liboak_a_SOURCES = \
    %D%/syscalls.c \
    %D%/crt0.S
