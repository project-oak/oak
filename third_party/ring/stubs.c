#include <stddef.h>

/**
 *
  Stub function for win64 error handler API call inserted by nasm.
  Stubbed as it is unavailable in UEFI.
  Ref: https://github.com/openssl/openssl/issues/12712.
  Inspired by: https://github.com/tianocore/edk2/blob/7c0ad2c33810ead45b7919f8f8d0e282dae52e71/CryptoPkg/Library/OpensslLib/X64/ApiHooks.c
**/
void *
__imp_RtlVirtualUnwind (
  void  *Args
  )
{
  return NULL;
}

/**
  Stub function for win64 routine used for exceedingly large variables.
  Inserted Mby inGW, stubbed as it is unavailable in UEFI.
  Ref 1: https://metricpanda.com/rival-fortress-update-45-dealing-with-__chkstk-__chkstk_ms-when-cross-compiling-for-windows/
  Ref 2: https://github.com/golang/go/issues/6305
  Inspired by: https://android.googlesource.com/platform/external/compiler-rt/+/ccaafe6%5E%21/#F1
**/
void ___chkstk_ms(void)
{
}

