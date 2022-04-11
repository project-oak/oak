#include <stddef.h>

/**
 *
  Stub function for win64 error handler API call inserted by nasm.
  Stubbed as it unavailable in UEFI.
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
  Stub function for win64 routine used for exceedomgy large variable calls.
  Inserted MinGW, stubbed as it unavailable in UEFI.
  Ref: https://metricpanda.com/rival-fortress-update-45-dealing-with-__chkstk-__chkstk_ms-when-cross-compiling-for-windows/
**/
void *
___chkstk_ms (
  void  *Args
  )
{
  return NULL;
}

