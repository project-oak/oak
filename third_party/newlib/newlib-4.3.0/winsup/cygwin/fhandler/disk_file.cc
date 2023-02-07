/* fhandler_disk_file.cc

This file is part of Cygwin.

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */

#include "winsup.h"
#include <winioctl.h>
#include <lm.h>
#include <stdlib.h>
#include <cygwin/acl.h>
#include <sys/statvfs.h>
#include "cygerrno.h"
#include "security.h"
#include "path.h"
#include "fhandler.h"
#include "dtable.h"
#include "cygheap.h"
#include "shared_info.h"
#include "pinfo.h"
#include "ntdll.h"
#include "tls_pbuf.h"
#include "devices.h"
#include "ldap.h"
#include <aio.h>
#include <cygwin/fs.h>

#define _LIBC
#include <dirent.h>

enum __DIR_mount_type {
  __DIR_mount_none = 0,
  __DIR_mount_target,
  __DIR_mount_virt_target
};

class __DIR_mounts
{
  int		 count;
  const char	*parent_dir;
  size_t	 parent_dir_len;
  UNICODE_STRING mounts[MAX_MOUNTS];
  bool		 found[MAX_MOUNTS + 3];
  UNICODE_STRING cygdrive;

#define __DIR_PROC	(MAX_MOUNTS)
#define __DIR_CYGDRIVE	(MAX_MOUNTS+1)
#define __DIR_DEV	(MAX_MOUNTS+2)

public:
  __DIR_mounts (const char *posix_path)
  : parent_dir (posix_path)
    {
      parent_dir_len = strlen (parent_dir);
      count = mount_table->get_mounts_here (parent_dir, parent_dir_len, mounts,
					    &cygdrive);
      rewind ();
    }
  ~__DIR_mounts ()
    {
      mount_table->free_mounts_here (mounts, count, &cygdrive);
    }
  /* For an entry within this dir, check if a mount point exists. */
  bool check_mount (PUNICODE_STRING fname)
    {
      if (parent_dir_len == 1)	/* root dir */
	{
	  if (RtlEqualUnicodeString (fname, &ro_u_proc, FALSE))
	    {
	      found[__DIR_PROC] = true;
	      return true;
	    }
	  if (RtlEqualUnicodeString (fname, &ro_u_dev, FALSE))
	    {
	      found[__DIR_DEV] = true;
	      return true;
	    }
	  if (fname->Length / sizeof (WCHAR) == mount_table->cygdrive_len - 2
	      && RtlEqualUnicodeString (fname, &cygdrive, FALSE))
	    {
	      found[__DIR_CYGDRIVE] = true;
	      return true;
	    }
	}
      for (int i = 0; i < count; ++i)
	if (RtlEqualUnicodeString (fname, &mounts[i], FALSE))
	  {
	    found[i] = true;
	    return true;
	  }
      return false;
    }
  /* On each call, add another mount point within this directory, which is
     not backed by a real subdir. */
  __DIR_mount_type check_missing_mount (PUNICODE_STRING retname = NULL)
    {
      for (int i = 0; i < count; ++i)
	if (!found[i])
	  {
	    found[i] = true;
	    if (retname)
	      *retname = mounts[i];
	    return __DIR_mount_target;
	  }
      if (parent_dir_len == 1)  /* root dir */
	{
	  if (!found[__DIR_PROC])
	    {
	      found[__DIR_PROC] = true;
	      if (retname)
		*retname = ro_u_proc;
	      return __DIR_mount_virt_target;
	    }
	  if (!found[__DIR_DEV])
	    {
	      found[__DIR_DEV] = true;
	      if (retname)
		*retname = ro_u_dev;
	      return __DIR_mount_virt_target;
	    }
	  if (!found[__DIR_CYGDRIVE])
	    {
	      found[__DIR_CYGDRIVE] = true;
	      if (cygdrive.Length > 0)
		{
		  if (retname)
		    *retname = cygdrive;
		  return __DIR_mount_virt_target;
		}
	    }
	}
      return __DIR_mount_none;
    }
    void rewind () { memset (found, 0, sizeof found); }
};

inline bool
path_conv::isgood_inode (ino_t ino) const
{
  /* If the FS doesn't support nonambiguous inode numbers anyway, bail out
     immediately. */
  if (!hasgood_inode ())
    return false;
  /* If the inode numbers are 64 bit numbers or if it's a local FS, they
     are to be trusted. */
  if (ino > UINT32_MAX || !isremote ())
    return true;
  /* The inode numbers returned from a remote NT4 NTFS are ephemeral
     32 bit numbers. */
  if (fs_is_ntfs ())
    return false;
  /* Starting with version 3.5.4, Samba returns the real inode numbers, if
     the file is on the same device as the root of the share (Samba function
     get_FileIndex).  32 bit inode numbers returned by older versions (likely
     < 3.0) are ephemeral. */
  if (fs_is_samba () && fs.samba_version () < 0x03050400)
    return false;
  /* Otherwise, trust the inode numbers unless proved otherwise. */
  return true;
}

/* Check reparse point to determine if it should be treated as a
   posix symlink or as a normal file/directory.  Logic is explained
   in detail in check_reparse_point_target in path.cc. */
static inline bool
readdir_check_reparse_point (POBJECT_ATTRIBUTES attr, bool remote)
{
  NTSTATUS status;
  HANDLE reph;
  IO_STATUS_BLOCK io;
  tmp_pathbuf tp;
  UNICODE_STRING symbuf;
  bool ret = false;

  status = NtOpenFile (&reph, READ_CONTROL, attr, &io, FILE_SHARE_VALID_FLAGS,
		       FILE_OPEN_FOR_BACKUP_INTENT | FILE_OPEN_REPARSE_POINT);
  if (NT_SUCCESS (status))
    {
      PREPARSE_DATA_BUFFER rp = (PREPARSE_DATA_BUFFER) tp.c_get ();
      ret = (check_reparse_point_target (reph, remote, rp, &symbuf) > 0);
      NtClose (reph);
    }
  return ret;
}

inline ino_t
path_conv::get_ino_by_handle (HANDLE hdl)
{
  IO_STATUS_BLOCK io;
  FILE_INTERNAL_INFORMATION fii;

  if (NT_SUCCESS (NtQueryInformationFile (hdl, &io, &fii, sizeof fii,
					  FileInternalInformation))
      && isgood_inode (fii.IndexNumber.QuadPart))
    return fii.IndexNumber.QuadPart;
  return 0;
}

/* For files on NFS shares, we request an EA of type NfsV3Attributes.
   This returns the content of a struct fattr3 as defined in RFC 1813.
   The content is the NFS equivalent of struct stat. so there's not much
   to do here except for copying. */
int
fhandler_base::fstat_by_nfs_ea (struct stat *buf)
{
  fattr3 *nfs_attr = pc.nfsattr ();
  PWCHAR domain;
  cyg_ldap cldap;
  bool ldap_open = false;

  if (get_handle ())
    {
      /* NFS stumbles over its own caching.  If you write to the file,
	 a subsequent fstat does not return the actual size of the file,
	 but the size at the time the handle has been opened.  Unless
	 access through another handle invalidates the caching within the
	 NFS client. */
      if (get_access () & GENERIC_WRITE)
	FlushFileBuffers (get_handle ());
      pc.get_finfo (get_handle ());
    }
  buf->st_dev = nfs_attr->fsid;
  buf->st_ino = nfs_attr->fileid;
  buf->st_mode = (nfs_attr->mode & 0xfff)
		 | nfs_type_mapping[nfs_attr->type & 7];
  buf->st_nlink = nfs_attr->nlink;
  if (cygheap->pg.nss_pwd_db ())
    {
      /* Try to map UNIX uid/gid to Cygwin uid/gid.  If there's no mapping in
	 the cache, try to fetch it from the configured RFC 2307 domain (see
	 last comment in cygheap_domain_info::init() for more information) and
	 add it to the mapping cache. */
      buf->st_uid = cygheap->ugid_cache.get_uid (nfs_attr->uid);
      if (buf->st_uid == ILLEGAL_UID)
	{
	  uid_t map_uid = ILLEGAL_UID;

	  domain = cygheap->dom.get_rfc2307_domain ();
	  if ((ldap_open = (cldap.open (domain) == NO_ERROR)))
	    map_uid = cldap.remap_uid (nfs_attr->uid);
	  if (map_uid == ILLEGAL_UID)
	    map_uid = MAP_UNIX_TO_CYGWIN_ID (nfs_attr->uid);
	  cygheap->ugid_cache.add_uid (nfs_attr->uid, map_uid);
	  buf->st_uid = map_uid;
	}
    }
  else /* fake files being owned by current user. */
    buf->st_uid = myself->uid;
  if (cygheap->pg.nss_grp_db ())
    {
      /* See above */
      buf->st_gid = cygheap->ugid_cache.get_gid (nfs_attr->gid);
      if (buf->st_gid == ILLEGAL_GID)
	{
	  gid_t map_gid = ILLEGAL_GID;

	  domain = cygheap->dom.get_rfc2307_domain ();
	  if ((ldap_open || cldap.open (domain) == NO_ERROR))
	    map_gid = cldap.remap_gid (nfs_attr->gid);
	  if (map_gid == ILLEGAL_GID)
	    map_gid = MAP_UNIX_TO_CYGWIN_ID (nfs_attr->gid);
	  cygheap->ugid_cache.add_gid (nfs_attr->gid, map_gid);
	  buf->st_gid = map_gid;
	}
    }
  else /* fake files being owned by current group. */
    buf->st_gid = myself->gid;
  buf->st_rdev = makedev (nfs_attr->rdev.specdata1,
			  nfs_attr->rdev.specdata2);
  buf->st_size = nfs_attr->size;
  buf->st_blksize = PREFERRED_IO_BLKSIZE;
  buf->st_blocks = (nfs_attr->used + S_BLKSIZE - 1) / S_BLKSIZE;
  buf->st_atim.tv_sec = nfs_attr->atime.tv_sec;
  buf->st_atim.tv_nsec = nfs_attr->atime.tv_nsec;
  buf->st_mtim.tv_sec = nfs_attr->mtime.tv_sec;
  buf->st_mtim.tv_nsec = nfs_attr->mtime.tv_nsec;
  buf->st_ctim.tv_sec = nfs_attr->ctime.tv_sec;
  buf->st_ctim.tv_nsec = nfs_attr->ctime.tv_nsec;
  return 0;
}

int
fhandler_base::fstat_by_handle (struct stat *buf)
{
  HANDLE h = get_stat_handle ();
  NTSTATUS status = 0;

  /* If the file has been opened for other purposes than stat, we can't rely
     on the information stored in pc.fai.  So we overwrite them here. */
  if (get_handle ())
    {
      status = pc.get_finfo (h);
      if (!NT_SUCCESS (status))
       {
	 debug_printf ("%y = NtQueryInformationFile(%S, FileAllInformation)",
		       status, pc.get_nt_native_path ());
	 return -1;
       }
    }
  if (pc.isgood_inode (pc.fai ()->InternalInformation.IndexNumber.QuadPart))
    ino = pc.fai ()->InternalInformation.IndexNumber.QuadPart;
  return fstat_helper (buf);
}

int
fhandler_base::fstat_by_name (struct stat *buf)
{
  NTSTATUS status;
  OBJECT_ATTRIBUTES attr;
  IO_STATUS_BLOCK io;
  UNICODE_STRING dirname;
  UNICODE_STRING basename;
  HANDLE dir;
  struct {
    FILE_ID_BOTH_DIR_INFORMATION fdi;
    WCHAR buf[NAME_MAX + 1];
  } fdi_buf;

  if (!ino && pc.hasgood_inode () && !pc.has_buggy_fileid_dirinfo ())
    {
      RtlSplitUnicodePath (pc.get_nt_native_path (), &dirname, &basename);
      InitializeObjectAttributes (&attr, &dirname, pc.objcaseinsensitive (),
				  NULL, NULL);
      status = NtOpenFile (&dir, SYNCHRONIZE | FILE_LIST_DIRECTORY,
			   &attr, &io, FILE_SHARE_VALID_FLAGS,
			   FILE_SYNCHRONOUS_IO_NONALERT
			   | FILE_OPEN_FOR_BACKUP_INTENT
			   | FILE_DIRECTORY_FILE);
      if (!NT_SUCCESS (status))
	debug_printf ("%y = NtOpenFile(%S)", status,
		      pc.get_nt_native_path ());
      else
	{
	  status = NtQueryDirectoryFile (dir, NULL, NULL, NULL, &io,
					 &fdi_buf.fdi, sizeof fdi_buf,
					 FileIdBothDirectoryInformation,
					 TRUE, &basename, TRUE);
	  NtClose (dir);
	  if (!NT_SUCCESS (status))
	    debug_printf ("%y = NtQueryDirectoryFile(%S)", status,
			  pc.get_nt_native_path ());
	  else
	    ino = fdi_buf.fdi.FileId.QuadPart;
	}
    }
  return fstat_helper (buf);
}

int
fhandler_base::fstat_fs (struct stat *buf)
{
  int res = -1;
  int oret;
  int open_flags = O_RDONLY | O_BINARY;

  if (get_stat_handle ())
    {
      if (!nohandle () && (!is_fs_special () || get_flags () & O_PATH))
	res = pc.fs_is_nfs () ? fstat_by_nfs_ea (buf) : fstat_by_handle (buf);
      if (res)
	res = fstat_by_name (buf);
      return res;
    }
  /* First try to open with generic read access.  This allows to read the file
     in fstat_helper (when checking for executability) without having to
     re-open it.  Opening a file can take a lot of time on network drives
     so we try to avoid that. */
  oret = open_fs (open_flags, 0);
  if (!oret)
    {
      query_open (query_read_attributes);
      oret = open_fs (open_flags, 0);
    }
  if (oret)
    {
      /* We now have a valid handle, regardless of the "nohandle" state.
	 Since fhandler_base::close only calls CloseHandle if !nohandle,
	 we have to set it to false before calling close and restore
	 the state afterwards. */
      res = pc.fs_is_nfs () ? fstat_by_nfs_ea (buf) : fstat_by_handle (buf);
      bool no_handle = nohandle ();
      nohandle (false);
      close_fs ();
      nohandle (no_handle);
      set_handle (NULL);
    }
  if (res)
    res = fstat_by_name (buf);

  return res;
}

int
fhandler_base::fstat_helper (struct stat *buf)
{
  IO_STATUS_BLOCK st;
  FILE_COMPRESSION_INFORMATION fci;
  HANDLE h = get_stat_handle ();
  PFILE_ALL_INFORMATION pfai = pc.fai ();
  ULONG attributes = pc.file_attributes ();

  to_timestruc_t (&pfai->BasicInformation.LastAccessTime, &buf->st_atim);
  to_timestruc_t (&pfai->BasicInformation.LastWriteTime, &buf->st_mtim);
  /* If the ChangeTime is 0, the underlying FS doesn't support this timestamp
     (FAT for instance).  If so, it's faked using LastWriteTime. */
  to_timestruc_t (pfai->BasicInformation.ChangeTime.QuadPart
		  ? &pfai->BasicInformation.ChangeTime
		  : &pfai->BasicInformation.LastWriteTime,
		  &buf->st_ctim);
  to_timestruc_t (&pfai->BasicInformation.CreationTime, &buf->st_birthtim);
  buf->st_dev = get_dev ();
  /* CV 2011-01-13: Observations on the Cygwin mailing list point to an
     interesting behaviour in some Windows versions.  Apparently the size of
     a directory is computed at the time the directory is first scanned.  This
     can result in two subsequent NtQueryInformationFile calls to return size
     0 in the first call and size > 0 in the second call.  This in turn can
     affect applications like newer tar.
     FIXME: Is the allocation size affected as well? */
  buf->st_size = pc.isdir ()
		 ? 0
		 : (off_t) pfai->StandardInformation.EndOfFile.QuadPart;
  /* The number of links to a directory includes the number of subdirectories
     in the directory, since all those subdirectories point to it.  However,
     this is painfully slow, so we do without it. */
  buf->st_nlink = pc.fai()->StandardInformation.NumberOfLinks;

  /* Enforce namehash as inode number on untrusted file systems. */
  buf->st_ino = ino ?: get_ino ();

  buf->st_blksize = PREFERRED_IO_BLKSIZE;

  if (buf->st_size == 0
      && pfai->StandardInformation.AllocationSize.QuadPart == 0LL)
    /* File is empty and no blocks are preallocated. */
    buf->st_blocks = 0;
  else if (pfai->StandardInformation.AllocationSize.QuadPart > 0LL)
    /* A successful NtQueryInformationFile returns the allocation size
       correctly for compressed and sparse files as well.
       Allocation size 0 is ignored here because (at least) Windows 10
       1607 always returns 0 for CompactOS compressed files. */
    buf->st_blocks = (pfai->StandardInformation.AllocationSize.QuadPart
		      + S_BLKSIZE - 1) / S_BLKSIZE;
  else if ((pfai->StandardInformation.AllocationSize.QuadPart == 0LL
	    || ::has_attribute (attributes, FILE_ATTRIBUTE_COMPRESSED
					  | FILE_ATTRIBUTE_SPARSE_FILE))
	   && h && !is_fs_special ()
	   && !NtQueryInformationFile (h, &st, (PVOID) &fci, sizeof fci,
				       FileCompressionInformation))
    /* Otherwise we request the actual amount of bytes allocated for
       compressed, sparsed and CompactOS files. */
    buf->st_blocks = (fci.CompressedFileSize.QuadPart + S_BLKSIZE - 1)
		     / S_BLKSIZE;
  else
    /* Otherwise compute no. of blocks from file size. */
    buf->st_blocks = (buf->st_size + S_BLKSIZE - 1) / S_BLKSIZE;

  buf->st_mode = 0;
  /* Using a side effect: get_file_attributes checks for directory.
     This is used, to set S_ISVTX, if needed.  */
  if (pc.isdir ())
    buf->st_mode = S_IFDIR;
  else if (pc.issymlink ())
    {
      buf->st_size = pc.get_symlink_length ();
      /* symlinks are everything for everyone! */
      buf->st_mode = S_IFLNK | S_IRWXU | S_IRWXG | S_IRWXO;
      get_file_attribute (h, pc, NULL,
			  &buf->st_uid, &buf->st_gid);
      goto done;
    }
  else if (pc.issocket ())
    buf->st_mode = S_IFSOCK;

  if (!get_file_attribute (h, pc, &buf->st_mode, &buf->st_uid, &buf->st_gid))
    {
      /* If read-only attribute is set, modify ntsec return value */
      if (::has_attribute (attributes, FILE_ATTRIBUTE_READONLY)
	  && !pc.isdir () && !pc.issymlink () && !pc.is_fs_special ())
	buf->st_mode &= ~(S_IWUSR | S_IWGRP | S_IWOTH);

      if (buf->st_mode & S_IFMT)
	/* nothing */;
      else if (!is_fs_special ())
	buf->st_mode |= S_IFREG;
      else
	{
	  buf->st_dev = buf->st_rdev = dev ();
	  buf->st_mode = dev ().mode ();
	  buf->st_size = 0;
	}
    }
  else
    {
      buf->st_mode |= STD_RBITS;

      if (!::has_attribute (attributes, FILE_ATTRIBUTE_READONLY))
	buf->st_mode |= STD_WBITS;
      /* | S_IWGRP | S_IWOTH; we don't give write to group etc */

      if (pc.isdir ())
	buf->st_mode |= S_IFDIR | STD_WBITS | STD_XBITS;
      else if (buf->st_mode & S_IFMT)
	/* nothing */;
      else if (is_fs_special ())
	{
	  buf->st_dev = buf->st_rdev = dev ();
	  buf->st_mode = dev ().mode ();
	  buf->st_size = 0;
	}
      else
	{
	  buf->st_mode |= S_IFREG;
	  /* Check suffix for executable file. */
	  if (pc.exec_state () != is_executable)
	    {
	      PUNICODE_STRING path = pc.get_nt_native_path ();

	      if (RtlEqualUnicodePathSuffix (path, &ro_u_exe, TRUE)
		  || RtlEqualUnicodePathSuffix (path, &ro_u_lnk, TRUE))
		pc.set_exec ();
	    }
	  /* No known suffix, check file header.  This catches binaries and
	     shebang scripts. */
	  if (pc.exec_state () == dont_know_if_executable)
	    {
	      OBJECT_ATTRIBUTES attr;
	      NTSTATUS status = 0;
	      IO_STATUS_BLOCK io;

	      /* We have to re-open the file.  Either the file is not opened
		 for reading, or the read will change the file position of the
		 original handle. */
	      status = NtOpenFile (&h, SYNCHRONIZE | FILE_READ_DATA,
				   pc.init_reopen_attr (attr, h), &io,
				   FILE_SHARE_VALID_FLAGS,
				   FILE_OPEN_FOR_BACKUP_INTENT
				   | FILE_SYNCHRONOUS_IO_NONALERT);
	      if (!NT_SUCCESS (status))
		debug_printf ("%y = NtOpenFile(%S)", status,
			      pc.get_nt_native_path ());
	      else
		{
		  LARGE_INTEGER off = { QuadPart:0LL };
		  char magic[3];

		  status = NtReadFile (h, NULL, NULL, NULL,
				       &io, magic, 3, &off, NULL);
		  if (!NT_SUCCESS (status))
		    debug_printf ("%y = NtReadFile(%S)", status,
				  pc.get_nt_native_path ());
		  else if (has_exec_chars (magic, io.Information))
		    {
		      /* Heureka, it's an executable */
		      pc.set_exec ();
		      buf->st_mode |= STD_XBITS;
		    }
		  NtClose (h);
		}
	    }
	}
      if (pc.exec_state () == is_executable)
	buf->st_mode |= STD_XBITS;

      /* This fakes the permissions of all files to match the current umask. */
      buf->st_mode &= ~(cygheap->umask);
      /* If the FS supports ACLs, we're here because we couldn't even open
	 the file for READ_CONTROL access.  Chances are high that the file's
	 security descriptor has no ACE for "Everyone", so we should not fake
	 any access for "others". */
      if (has_acls ())
	buf->st_mode &= ~(S_IROTH | S_IWOTH | S_IXOTH);
    }

 done:
  syscall_printf ("0 = fstat (%S, %p) st_size=%D, st_mode=0%o, st_ino=%D"
		  "st_atim=%lx.%lx st_ctim=%lx.%lx "
		  "st_mtim=%lx.%lx st_birthtim=%lx.%lx",
		  pc.get_nt_native_path (), buf,
		  buf->st_size, buf->st_mode, buf->st_ino,
		  buf->st_atim.tv_sec, buf->st_atim.tv_nsec,
		  buf->st_ctim.tv_sec, buf->st_ctim.tv_nsec,
		  buf->st_mtim.tv_sec, buf->st_mtim.tv_nsec,
		  buf->st_birthtim.tv_sec, buf->st_birthtim.tv_nsec);
  return 0;
}

int
fhandler_disk_file::fstat (struct stat *buf)
{
  return fstat_fs (buf);
}

int
fhandler_disk_file::fstatvfs (struct statvfs *sfs)
{
  int ret = -1, opened = 0;
  IO_STATUS_BLOCK io;
  /* We must not use the stat handle here, even if it exists.  The handle
     has been opened with FILE_OPEN_REPARSE_POINT, thus, in case of a volume
     mount point, it points to the FS of the mount point, rather than to the
     mounted FS. */
  HANDLE fh = get_handle ();

  if (!fh)
    {
      OBJECT_ATTRIBUTES attr;
      opened = NT_SUCCESS (NtOpenFile (&fh, READ_CONTROL,
				       pc.get_object_attr (attr, sec_none_nih),
				       &io, FILE_SHARE_VALID_FLAGS,
				       FILE_OPEN_FOR_BACKUP_INTENT));
      if (!opened)
	{
	  /* Can't open file.  Try again with parent dir. */
	  UNICODE_STRING dirname;
	  RtlSplitUnicodePath (pc.get_nt_native_path (), &dirname, NULL);
	  attr.ObjectName = &dirname;
	  opened = NT_SUCCESS (NtOpenFile (&fh, READ_CONTROL, &attr, &io,
					   FILE_SHARE_VALID_FLAGS,
					   FILE_OPEN_FOR_BACKUP_INTENT));
	  if (!opened)
	    goto out;
	}
    }

  ret = fstatvfs_by_handle (fh, sfs);
out:
  if (opened)
    NtClose (fh);
  syscall_printf ("%d = fstatvfs(%s, %p)", ret, get_name (), sfs);
  return ret;
}

int
fhandler_base::fstatvfs_by_handle (HANDLE fh, struct statvfs *sfs)
{
  int ret = -1;
  NTSTATUS status;
  IO_STATUS_BLOCK io;
  FILE_FS_FULL_SIZE_INFORMATION full_fsi;

  sfs->f_files = ULONG_MAX;
  sfs->f_ffree = ULONG_MAX;
  sfs->f_favail = ULONG_MAX;
  sfs->f_fsid = pc.fs_serial_number ();
  sfs->f_flag = pc.fs_flags ();
  sfs->f_namemax = pc.fs_name_len ();
  /* Get allocation related information. */
  status = NtQueryVolumeInformationFile (fh, &io, &full_fsi, sizeof full_fsi,
					 FileFsFullSizeInformation);
  if (NT_SUCCESS (status))
    {
      sfs->f_bsize = full_fsi.BytesPerSector * full_fsi.SectorsPerAllocationUnit;
      sfs->f_frsize = sfs->f_bsize;
      sfs->f_blocks = (fsblkcnt_t) full_fsi.TotalAllocationUnits.QuadPart;
      sfs->f_bfree = (fsblkcnt_t)
		     full_fsi.ActualAvailableAllocationUnits.QuadPart;
      sfs->f_bavail = (fsblkcnt_t)
		      full_fsi.CallerAvailableAllocationUnits.QuadPart;
      if (sfs->f_bfree > sfs->f_bavail)
	{
	  /* Quotas active.  We can't trust TotalAllocationUnits. */
	  NTFS_VOLUME_DATA_BUFFER nvdb;

	  status = NtFsControlFile (fh, NULL, NULL, NULL, &io,
				    FSCTL_GET_NTFS_VOLUME_DATA,
				    NULL, 0, &nvdb, sizeof nvdb);
	  if (!NT_SUCCESS (status))
	    debug_printf ("%y = NtFsControlFile(%S, FSCTL_GET_NTFS_VOLUME_DATA)",
			  status, pc.get_nt_native_path ());
	  else
	    sfs->f_blocks = (fsblkcnt_t) nvdb.TotalClusters.QuadPart;
	}
      ret = 0;
    }
  else if (status == STATUS_INVALID_PARAMETER /* Netapp */
	   || status == STATUS_INVALID_INFO_CLASS)
    {
      FILE_FS_SIZE_INFORMATION fsi;
      status = NtQueryVolumeInformationFile (fh, &io, &fsi, sizeof fsi,
					     FileFsSizeInformation);
      if (NT_SUCCESS (status))
	{
	  sfs->f_bsize = fsi.BytesPerSector * fsi.SectorsPerAllocationUnit;
	  sfs->f_frsize = sfs->f_bsize;
	  sfs->f_blocks = (fsblkcnt_t) fsi.TotalAllocationUnits.QuadPart;
	  sfs->f_bfree = sfs->f_bavail =
	    (fsblkcnt_t) fsi.AvailableAllocationUnits.QuadPart;
	  ret = 0;
	}
      else
	debug_printf ("%y = NtQueryVolumeInformationFile"
		      "(%S, FileFsSizeInformation)",
		      status, pc.get_nt_native_path ());
    }
  else
    debug_printf ("%y = NtQueryVolumeInformationFile"
		  "(%S, FileFsFullSizeInformation)",
		  status, pc.get_nt_native_path ());
  return ret;
}

int
fhandler_disk_file::fchmod (mode_t mode)
{
  int ret = -1;
  int oret = 0;
  NTSTATUS status;
  IO_STATUS_BLOCK io;

  if (pc.is_fs_special ())
    return chmod_device (pc, mode);

  if (!get_handle ())
    {
      query_open (query_write_dac);
      if (!(oret = open (O_BINARY, 0)))
	{
	  /* Need WRITE_DAC to write ACLs. */
	  if (pc.has_acls ())
	    return -1;
	  /* Otherwise FILE_WRITE_ATTRIBUTES is sufficient. */
	  query_open (query_write_attributes);
	  if (!(oret = open (O_BINARY, 0)))
	    return -1;
	}
    }

  if (pc.fs_is_nfs ())
    {
      /* chmod on NFS shares works by writing an EA of type NfsV3Attributes.
	 Only type and mode have to be set.  Apparently type isn't checked
	 for consistency, so it's sufficent to set it to NF3REG all the time. */
      struct {
	FILE_FULL_EA_INFORMATION ffei;
	char buf[sizeof (NFS_V3_ATTR) + sizeof (fattr3)];
      } ffei_buf;
      ffei_buf.ffei.NextEntryOffset = 0;
      ffei_buf.ffei.Flags = 0;
      ffei_buf.ffei.EaNameLength = sizeof (NFS_V3_ATTR) - 1;
      ffei_buf.ffei.EaValueLength = sizeof (fattr3);
      strcpy (ffei_buf.ffei.EaName, NFS_V3_ATTR);
      fattr3 *nfs_attr = (fattr3 *) (ffei_buf.ffei.EaName
				     + ffei_buf.ffei.EaNameLength + 1);
      memset (nfs_attr, 0, sizeof (fattr3));
      nfs_attr->type = NF3REG;
      nfs_attr->mode = mode;
      status = NtSetEaFile (get_handle (), &io,
			    &ffei_buf.ffei, sizeof ffei_buf);
      if (!NT_SUCCESS (status))
	__seterrno_from_nt_status (status);
      else
	ret = 0;
      goto out;
    }

  if (pc.has_acls ())
    {
      security_descriptor sd, sd_ret;
      uid_t uid;
      gid_t gid;
      tmp_pathbuf tp;
      aclent_t *aclp;
      bool standard_acl = false;
      int nentries, idx;

      if (!get_file_sd (get_handle (), pc, sd, false))
	{
	  aclp = (aclent_t *) tp.c_get ();
	  if ((nentries = get_posix_access (sd, NULL, &uid, &gid,
					    aclp, MAX_ACL_ENTRIES,
					    &standard_acl)) >= 0)
	    {
	      /* Overwrite ACL permissions as required by POSIX 1003.1e
		 draft 17. */
	      aclp[0].a_perm = (mode >> 6) & S_IRWXO;

	      /* POSIXly correct: If CLASS_OBJ is present, chmod only modifies
		 CLASS_OBJ, not GROUP_OBJ.

		 Deliberate deviation from POSIX 1003.1e:  If the ACL is a
		 "standard" ACL, that is, it only contains POSIX permissions
		 as well as entries for the Administrators group and SYSTEM,
		 then it's kind of a POSIX-only ACL in a twisted, Windowsy
		 way.  If so, we change GROUP_OBJ and CLASS_OBJ perms. */
	      if (standard_acl
		  && (idx = searchace (aclp, nentries, GROUP_OBJ)) >= 0)
		aclp[idx].a_perm = (mode >> 3) & S_IRWXO;
	      if (nentries > MIN_ACL_ENTRIES
		  && (idx = searchace (aclp, nentries, CLASS_OBJ)) >= 0)
		aclp[idx].a_perm = (mode >> 3) & S_IRWXO;

	      if ((idx = searchace (aclp, nentries, OTHER_OBJ)) >= 0)
		aclp[idx].a_perm = mode & S_IRWXO;
	      if (pc.isdir ())
		mode |= S_IFDIR;
	      if (set_posix_access (mode, uid, gid, aclp, nentries, sd_ret,
				    pc.fs_is_samba ()))
		ret = set_file_sd (get_handle (), pc, sd_ret, false);
	    }
	}
    }

  /* If the mode has any write bits set, the DOS R/O flag is in the way. */
  if (mode & (S_IWUSR | S_IWGRP | S_IWOTH))
    pc &= (DWORD) ~FILE_ATTRIBUTE_READONLY;
  else if (!pc.has_acls ())	/* Never set DOS R/O if security is used. */
    pc |= (DWORD) FILE_ATTRIBUTE_READONLY;
  if (S_ISSOCK (mode))
    pc |= (DWORD) FILE_ATTRIBUTE_SYSTEM;

  status = NtSetAttributesFile (get_handle (), pc.file_attributes ());
  /* MVFS needs a good amount of kicking to be convinced that it has to write
     back metadata changes and to invalidate the cached metadata information
     stored for the given handle.  This method to open a second handle to
     the file and write the same metadata information twice has been found
     experimentally: http://cygwin.com/ml/cygwin/2009-07/msg00533.html */
  if (pc.fs_is_mvfs () && NT_SUCCESS (status) && !oret)
    {
      OBJECT_ATTRIBUTES attr;
      HANDLE fh;

      if (NT_SUCCESS (NtOpenFile (&fh, FILE_WRITE_ATTRIBUTES,
				  pc.init_reopen_attr (attr, get_handle ()),
				  &io, FILE_SHARE_VALID_FLAGS,
				  FILE_OPEN_FOR_BACKUP_INTENT)))
	{
	  NtSetAttributesFile (fh, pc.file_attributes ());
	  NtClose (fh);
	}
    }
  /* Correct NTFS security attributes have higher priority */
  if (!pc.has_acls ())
    {
      if (!NT_SUCCESS (status))
	__seterrno_from_nt_status (status);
      else
	ret = 0;
    }

out:
  if (oret)
    close_fs ();

  return ret;
}

int
fhandler_disk_file::fchown (uid_t uid, gid_t gid)
{
  int oret = 0;
  int ret = -1;
  security_descriptor sd, sd_ret;
  mode_t attr = pc.isdir () ? S_IFDIR : 0;
  uid_t old_uid;
  gid_t old_gid;
  tmp_pathbuf tp;
  aclent_t *aclp;
  int nentries;

  if (!pc.has_acls ())
    {
      /* fake - if not supported, pretend we're like win95
	 where it just works */
      /* FIXME: Could be supported on NFS when user->uid mapping is in place. */
      return 0;
    }

  if (!get_handle ())
    {
      query_open (query_write_control);
      if (!(oret = fhandler_disk_file::open (O_BINARY, 0)))
	return -1;
    }

  if (get_file_sd (get_handle (), pc, sd, false))
    goto out;

  aclp = (aclent_t *) tp.c_get ();
  if ((nentries = get_posix_access (sd, &attr, &old_uid, &old_gid,
				    aclp, MAX_ACL_ENTRIES)) < 0)
    goto out;

  /* According to POSIX, chown can be a no-op if uid is (uid_t)-1 and
     gid is (gid_t)-1.  Otherwise, even if uid and gid are unchanged,
     we must ensure that ctime is updated. */
  if (uid == ILLEGAL_UID && gid == ILLEGAL_GID)
    {
      ret = 0;
      goto out;
    }
  if (uid == ILLEGAL_UID)
    uid = old_uid;
  else if (gid == ILLEGAL_GID)
    gid = old_gid;

  /* Windows ACLs can contain permissions for one group, while being owned by
     another user/group.  The permission bits returned above are pretty much
     useless then.  Creating a new ACL with these useless permissions results
     in a potentially broken symlink.  So what we do here is to set the
     underlying permissions of symlinks to a sensible value which allows the
     world to read the symlink and only the new owner to change it. */
  if (pc.issymlink ())
    for (int idx = 0; idx < nentries; ++idx)
      {
	aclp[idx].a_perm |= S_IROTH;
	if (aclp[idx].a_type & USER_OBJ)
	  aclp[idx].a_perm |= S_IWOTH;
      }

  if (set_posix_access (attr, uid, gid, aclp, nentries, sd_ret,
			pc.fs_is_samba ()))
    ret = set_file_sd (get_handle (), pc, sd_ret, true);

  /* If you're running a Samba server with no winbind, the uid<->SID mapping
     is disfunctional.  Even trying to chown to your own account fails since
     the account used on the server is the UNIX account which gets used for
     the standard user mapping.  This is a default mechanism which doesn't
     know your real Windows SID.  There are two possible error codes in
     different Samba releases for this situation, one of them unfortunately
     the not very significant STATUS_ACCESS_DENIED.  Instead of relying on
     the error codes, we're using the below very simple heuristic.
     If set_file_sd failed, and the original user account was either already
     unknown, or one of the standard UNIX accounts, we're faking success. */
  if (ret == -1 && pc.fs_is_samba ())
    {
      PSID sid;

      if (uid == old_uid
	  || ((sid = sidfromuid (old_uid, NULL)) != NO_SID
	      && RtlEqualPrefixSid (sid,
				    well_known_samba_unix_user_fake_sid)))
	{
	  debug_printf ("Faking chown worked on standalone Samba");
	  ret = 0;
	}
    }

out:
  if (oret)
    close_fs ();

  return ret;
}

int
fhandler_disk_file::facl (int cmd, int nentries, aclent_t *aclbufp)
{
  int res = -1;
  int oret = 0;

  if (!pc.has_acls ())
    {
cant_access_acl:
      switch (cmd)
	{

	  case SETACL:
	    /* Open for writing required to be able to set ctime
	       (even though setting the ACL is just pretended). */
	    if (!get_handle ())
	      oret = open (O_WRONLY | O_BINARY, 0);
	    res = 0;
	    break;
	  case GETACL:
	    if (!aclbufp)
	      set_errno (EFAULT);
	    else if (nentries < MIN_ACL_ENTRIES)
	      set_errno (ENOSPC);
	    else
	      {
		struct stat st;
		if (!fstat (&st))
		  {
		    aclbufp[0].a_type = USER_OBJ;
		    aclbufp[0].a_id = st.st_uid;
		    aclbufp[0].a_perm = (st.st_mode & S_IRWXU) >> 6;
		    aclbufp[1].a_type = GROUP_OBJ;
		    aclbufp[1].a_id = st.st_gid;
		    aclbufp[1].a_perm = (st.st_mode & S_IRWXG) >> 3;
		    aclbufp[2].a_type = OTHER_OBJ;
		    aclbufp[2].a_id = ILLEGAL_GID;
		    aclbufp[2].a_perm = st.st_mode & S_IRWXO;
		    res = MIN_ACL_ENTRIES;
		  }
	      }
	    break;
	  case GETACLCNT:
	    res = MIN_ACL_ENTRIES;
	    break;
	  default:
	    set_errno (EINVAL);
	    break;
	}
    }
  else
    {
      if ((cmd == SETACL && !get_handle ())
	  || (cmd != SETACL && !get_stat_handle ()))
	{
	  query_open (cmd == SETACL ? query_write_dac : query_read_control);
	  if (!(oret = open (O_BINARY, 0)))
	    {
	      if (cmd == GETACL || cmd == GETACLCNT)
		goto cant_access_acl;
	      return -1;
	    }
	}
      switch (cmd)
	{
	  case SETACL:
	    if (!aclsort (nentries, 0, aclbufp))
	      {
		bool rw = false;
		res = setacl (get_handle (), pc, nentries, aclbufp, rw);
		if (rw)
		  {
		    IO_STATUS_BLOCK io;
		    FILE_BASIC_INFORMATION fbi;
		    fbi.CreationTime.QuadPart
		    = fbi.LastAccessTime.QuadPart
		    = fbi.LastWriteTime.QuadPart
		    = fbi.ChangeTime.QuadPart = 0LL;
		    fbi.FileAttributes = (pc.file_attributes ()
					  & ~FILE_ATTRIBUTE_READONLY)
					 ?: FILE_ATTRIBUTE_NORMAL;
		    NtSetInformationFile (get_handle (), &io, &fbi, sizeof fbi,
					  FileBasicInformation);
		  }
	      }
	    break;
	  case GETACL:
	    if (!aclbufp)
	      set_errno(EFAULT);
	    else {
	      res = getacl (get_stat_handle (), pc, nentries, aclbufp);
	      /* For this ENOSYS case, see security.cc:get_file_attribute(). */
	      if (res == -1 && get_errno () == ENOSYS)
		goto cant_access_acl;
            }
	    break;
	  case GETACLCNT:
	    res = getacl (get_stat_handle (), pc, 0, NULL);
	    /* Ditto. */
	    if (res == -1 && get_errno () == ENOSYS)
	      goto cant_access_acl;
	    break;
	  default:
	    set_errno (EINVAL);
	    break;
	}
    }

  if (oret)
    close_fs ();

  return res;
}

ssize_t
fhandler_disk_file::fgetxattr (const char *name, void *value, size_t size)
{
  if (pc.is_fs_special ())
    {
      set_errno (ENOTSUP);
      return -1;
    }
  return read_ea (get_handle (), pc, name, (char *) value, size);
}

int
fhandler_disk_file::fsetxattr (const char *name, const void *value, size_t size,
			       int flags)
{
  if (pc.is_fs_special ())
    {
      set_errno (ENOTSUP);
      return -1;
    }
  return write_ea (get_handle (), pc, name, (const char *) value, size, flags);
}

int
fhandler_disk_file::fadvise (off_t offset, off_t length, int advice)
{
  if (advice < POSIX_FADV_NORMAL || advice > POSIX_FADV_NOREUSE)
    return EINVAL;

  /* Windows only supports advice flags for the whole file.  We're using
     a simplified test here so that we don't have to ask for the actual
     file size.  Length == 0 means all bytes starting at offset anyway.
     So we only actually follow the advice, if it's given for offset == 0. */
  if (offset != 0)
    return 0;

  /* We only support normal and sequential mode for now.  Everything which
     is not POSIX_FADV_SEQUENTIAL is treated like POSIX_FADV_NORMAL. */
  if (advice != POSIX_FADV_SEQUENTIAL)
    advice = POSIX_FADV_NORMAL;

  IO_STATUS_BLOCK io;
  FILE_MODE_INFORMATION fmi;
  NTSTATUS status = NtQueryInformationFile (get_handle (), &io,
					    &fmi, sizeof fmi,
					    FileModeInformation);
  if (NT_SUCCESS (status))
    {
      fmi.Mode &= ~FILE_SEQUENTIAL_ONLY;
      if (advice == POSIX_FADV_SEQUENTIAL)
	fmi.Mode |= FILE_SEQUENTIAL_ONLY;
      status = NtSetInformationFile (get_handle (), &io, &fmi, sizeof fmi,
				     FileModeInformation);
      if (NT_SUCCESS (status))
	return 0;
      __seterrno_from_nt_status (status);
    }

  return geterrno_from_nt_status (status);
}

int
fhandler_disk_file::ftruncate (off_t length, bool allow_truncate)
{
  int res = 0;

  if (length < 0 || !get_handle ())
    res = EINVAL;
  else if (pc.isdir ())
    res = EISDIR;
  else if (!(get_access () & GENERIC_WRITE))
    res = EBADF;
  else
    {
      NTSTATUS status;
      IO_STATUS_BLOCK io;
      FILE_STANDARD_INFORMATION fsi;
      FILE_END_OF_FILE_INFORMATION feofi;

      status = NtQueryInformationFile (get_handle (), &io, &fsi, sizeof fsi,
				       FileStandardInformation);
      if (!NT_SUCCESS (status))
	return geterrno_from_nt_status (status);

      /* If called through posix_fallocate, silently succeed if length
	 is less than the file's actual length. */
      if (!allow_truncate && length < fsi.EndOfFile.QuadPart)
	return 0;

      feofi.EndOfFile.QuadPart = length;
      /* Create sparse files only when called through ftruncate, not when
	 called through posix_fallocate. */
      if (allow_truncate && pc.support_sparse ()
	  && !has_attribute (FILE_ATTRIBUTE_SPARSE_FILE)
	  && length >= fsi.EndOfFile.QuadPart + (128 * 1024))
	{
	  status = NtFsControlFile (get_handle (), NULL, NULL, NULL, &io,
				    FSCTL_SET_SPARSE, NULL, 0, NULL, 0);
	  if (NT_SUCCESS (status))
	    pc.file_attributes (pc.file_attributes ()
			        | FILE_ATTRIBUTE_SPARSE_FILE);
	  syscall_printf ("%y = NtFsControlFile(%S, FSCTL_SET_SPARSE)",
			  status, pc.get_nt_native_path ());
	}
      status = NtSetInformationFile (get_handle (), &io,
				     &feofi, sizeof feofi,
				     FileEndOfFileInformation);
      if (!NT_SUCCESS (status))
	res = geterrno_from_nt_status (status);
    }
  return res;
}

int
fhandler_disk_file::link (const char *newpath)
{
  size_t nlen = strlen (newpath);
  path_conv newpc (newpath, PC_SYM_NOFOLLOW | PC_POSIX | PC_NULLEMPTY, stat_suffixes);
  if (newpc.error)
    {
      set_errno (newpc.error);
      return -1;
    }

  if (newpc.exists ())
    {
      syscall_printf ("file '%S' exists?", newpc.get_nt_native_path ());
      set_errno (EEXIST);
      return -1;
    }

  if (isdirsep (newpath[nlen - 1]) || has_dot_last_component (newpath, false))
    {
      set_errno (ENOENT);
      return -1;
    }

  char new_buf[nlen + 5];
  if (!newpc.error)
    {
      /* If the original file is a lnk special file,
	 and if the original file has a .lnk suffix, add one to the hardlink
	 as well. */
      if (pc.is_lnk_special ()
	  && RtlEqualUnicodePathSuffix (pc.get_nt_native_path (),
					&ro_u_lnk, TRUE))
	{
	  /* Shortcut hack. */
	  stpcpy (stpcpy (new_buf, newpath), ".lnk");
	  newpath = new_buf;
	  newpc.check (newpath, PC_SYM_NOFOLLOW);
	}
      else if (!pc.isdir ()
	       && pc.is_binary ()
	       && RtlEqualUnicodePathSuffix (pc.get_nt_native_path (),
					     &ro_u_exe, TRUE)
	       && !RtlEqualUnicodePathSuffix (newpc.get_nt_native_path (),
					      &ro_u_exe, TRUE))
	{
	  /* Executable hack. */
	  stpcpy (stpcpy (new_buf, newpath), ".exe");
	  newpath = new_buf;
	  newpc.check (newpath, PC_SYM_NOFOLLOW);
	}
    }

  /* We only need READ_CONTROL access so the handle returned in pc is
     sufficient.  And if the file couldn't be opened with READ_CONTROL
     access in path_conv, we won't be able to do it here anyway. */
  HANDLE fh = get_stat_handle ();
  if (!fh)
    {
      set_errno (EACCES);
      return -1;
    }
  PUNICODE_STRING tgt = newpc.get_nt_native_path ();
  ULONG size = sizeof (FILE_LINK_INFORMATION) + tgt->Length;
  PFILE_LINK_INFORMATION pfli = (PFILE_LINK_INFORMATION) alloca (size);
  pfli->ReplaceIfExists = FALSE;
  pfli->RootDirectory = NULL;
  memcpy (pfli->FileName, tgt->Buffer, pfli->FileNameLength = tgt->Length);

  NTSTATUS status;
  IO_STATUS_BLOCK io;
  status = NtSetInformationFile (fh, &io, pfli, size, FileLinkInformation);
  if (!NT_SUCCESS (status))
    {
      if (status == STATUS_INVALID_DEVICE_REQUEST
	  || status == STATUS_NOT_SUPPORTED)
	/* FS doesn't support hard links.  Linux returns EPERM. */
	set_errno (EPERM);
      else
	__seterrno_from_nt_status (status);
      return -1;
    }
  else if ((pc.file_attributes () & O_TMPFILE_FILE_ATTRS)
	   == O_TMPFILE_FILE_ATTRS)
    {
      /* An O_TMPFILE file has FILE_ATTRIBUTE_TEMPORARY and
	 FILE_ATTRIBUTE_HIDDEN set.  After a successful hardlink the file is
	 not temporary anymore in the usual sense.  So we remove these
	 attributes here.

	 Note that we don't create a reopen attribute for the original
	 link but rather a normal attribute for the just created link.
	 The reason is a curious behaviour of Windows:  If we remove the
	 O_TMPFILE attributes on the original link, the new link will not
	 show up in file system listings (not even native ones from , e.g.,
	 `cmd /c dir'), long after the original link has been closed and
	 removed.  The file and its metadata will be kept in memory only
	 as long as Windows sees fit.  By opening the new link, we request
	 the attribute changes on the new link, so after closing it Windows
	 will have an increased interest to write back the metadata. */
      OBJECT_ATTRIBUTES attr;
      status = NtOpenFile (&fh, FILE_WRITE_ATTRIBUTES,
			   newpc.get_object_attr (attr, sec_none_nih), &io,
			   FILE_SHARE_VALID_FLAGS, FILE_OPEN_FOR_BACKUP_INTENT);
      if (!NT_SUCCESS (status))
	debug_printf ("Opening for removing TEMPORARY attrib failed, "
		      "status = %y", status);
      else
	{
	  FILE_BASIC_INFORMATION fbi;

	  fbi.CreationTime.QuadPart = fbi.LastAccessTime.QuadPart
	  = fbi.LastWriteTime.QuadPart = fbi.ChangeTime.QuadPart = 0LL;
	  fbi.FileAttributes = (pc.file_attributes () & ~O_TMPFILE_FILE_ATTRS)
			       ?: FILE_ATTRIBUTE_NORMAL;
	  status = NtSetInformationFile (fh, &io, &fbi, sizeof fbi,
					 FileBasicInformation);
	  if (!NT_SUCCESS (status))
	    debug_printf ("Removing the TEMPORARY attrib failed, status = %y",
			  status);
	  NtClose (fh);
	}
    }
  return 0;
}

int
fhandler_disk_file::utimens (const struct timespec *tvp)
{
  return utimens_fs (tvp);
}

int
fhandler_base::utimens_fs (const struct timespec *tvp)
{
  struct timespec timeofday;
  struct timespec tmp[2];
  bool closeit = false;

  if (!get_handle ())
    {
      query_open (query_write_attributes);
      if (!open_fs (O_BINARY, 0))
	{
	  /* It's documented in MSDN that FILE_WRITE_ATTRIBUTES is sufficient
	     to change the timestamps.  Unfortunately it's not sufficient for a
	     remote HPFS which requires GENERIC_WRITE, so we just retry to open
	     for writing, though this fails for R/O files of course. */
	  query_open (no_query);
	  if (!open_fs (O_WRONLY | O_BINARY, 0))
	    {
	      syscall_printf ("Opening file failed");
	      return -1;
	    }
	}
      closeit = true;
    }

  clock_gettime (CLOCK_REALTIME, &timeofday);
  if (!tvp)
    tmp[1] = tmp[0] = timeofday;
  else
    {
      if ((tvp[0].tv_nsec < UTIME_NOW || tvp[0].tv_nsec >= NSPERSEC)
	  || (tvp[1].tv_nsec < UTIME_NOW || tvp[1].tv_nsec >= NSPERSEC))
	{
	  if (closeit)
	    close_fs ();
	  set_errno (EINVAL);
	  return -1;
	}
      tmp[0] = (tvp[0].tv_nsec == UTIME_NOW) ? timeofday : tvp[0];
      tmp[1] = (tvp[1].tv_nsec == UTIME_NOW) ? timeofday : tvp[1];
    }
  debug_printf ("incoming lastaccess %ly %ly", tmp[0].tv_sec, tmp[0].tv_nsec);

  IO_STATUS_BLOCK io;
  FILE_BASIC_INFORMATION fbi;

  fbi.CreationTime.QuadPart = 0LL;
  /* UTIME_OMIT is handled in timespec_to_filetime by setting FILETIME to 0. */
  timespec_to_filetime (&tmp[0], &fbi.LastAccessTime);
  timespec_to_filetime (&tmp[1], &fbi.LastWriteTime);
  fbi.ChangeTime.QuadPart = 0LL;
  fbi.FileAttributes = 0;
  NTSTATUS status = NtSetInformationFile (get_handle (), &io, &fbi, sizeof fbi,
					  FileBasicInformation);
  /* For this special case for MVFS see the comment in
     fhandler_disk_file::fchmod. */
  if (pc.fs_is_mvfs () && NT_SUCCESS (status) && !closeit)
    {
      OBJECT_ATTRIBUTES attr;
      HANDLE fh;

      if (NT_SUCCESS (NtOpenFile (&fh, FILE_WRITE_ATTRIBUTES,
				  pc.init_reopen_attr (attr, get_handle ()),
				  &io, FILE_SHARE_VALID_FLAGS,
				  FILE_OPEN_FOR_BACKUP_INTENT)))
	{
	  NtSetInformationFile (fh, &io, &fbi, sizeof fbi,
				FileBasicInformation);
	  NtClose (fh);
	}
    }
  if (closeit)
    close_fs ();
  /* Opening a directory on a 9x share from a NT machine works(!), but
     then NtSetInformationFile fails with STATUS_NOT_SUPPORTED.  Oh well... */
  if (!NT_SUCCESS (status) && status != STATUS_NOT_SUPPORTED)
    {
      __seterrno_from_nt_status (status);
      return -1;
    }
  return 0;
}

fhandler_disk_file::fhandler_disk_file () :
  fhandler_base (), prw_handle (NULL)
{
}

fhandler_disk_file::fhandler_disk_file (path_conv &pc) :
  fhandler_base (), prw_handle (NULL)
{
  set_name (pc);
}

int
fhandler_disk_file::open (int flags, mode_t mode)
{
  return open_fs (flags, mode);
}

int
fhandler_disk_file::close ()
{
  /* Close extra pread/pwrite handle, if it exists. */
  if (prw_handle)
    NtClose (prw_handle);
  return fhandler_base::close ();
}

int
fhandler_disk_file::fcntl (int cmd, intptr_t arg)
{
  int res;

  switch (cmd)
    {
    case F_LCK_MANDATORY:	/* Mandatory locking only works on files. */
      mandatory_locking (!!arg);
      need_fork_fixup (true);
      res = 0;
      break;
    default:
      res = fhandler_base::fcntl (cmd, arg);
      break;
    }
  return res;
}

int
fhandler_disk_file::dup (fhandler_base *child, int flags)
{
  fhandler_disk_file *fhc = (fhandler_disk_file *) child;

  int ret = fhandler_base::dup (child, flags);
  if (!ret && prw_handle
      && !DuplicateHandle (GetCurrentProcess (), prw_handle,
			   GetCurrentProcess (), &fhc->prw_handle,
			   0, FALSE, DUPLICATE_SAME_ACCESS))
    fhc->prw_handle = NULL;
  return ret;
}

void
fhandler_disk_file::fixup_after_fork (HANDLE parent)
{
  prw_handle = NULL;
  mandatory_locking (false);
  fhandler_base::fixup_after_fork (parent);
}

int
fhandler_base::open_fs (int flags, mode_t mode)
{
  /* Unfortunately NT allows to open directories for writing, but that's
     disallowed according to SUSv3. */
  if (pc.isdir () && (flags & O_ACCMODE) != O_RDONLY)
    {
      set_errno (EISDIR);
      return 0;
    }

  bool new_file = !exists ();

  int res = fhandler_base::open (flags, mode);
  if (res)
    {
      /* The file info in pc is wrong at this point for newly created files.
	 Refresh it before fetching any file info. */
      if (new_file)
	pc.get_finfo (get_handle ());

      if (pc.isgood_inode (pc.get_ino ()))
	ino = pc.get_ino ();
    }

  syscall_printf ("%d = fhandler_disk_file::open(%S, %y)", res,
		  pc.get_nt_native_path (), flags);
  return res;
}

/* POSIX demands that pread/pwrite don't change the current file position.
   While NtReadFile/NtWriteFile support atomic seek-and-io, both change the
   file pointer if the file handle has been opened for synchonous I/O.
   Using this handle for pread/pwrite would break atomicity, because the
   read/write operation would have to be followed by a seek back to the old
   file position.  What we do is to open another handle to the file on the
   first call to either pread or pwrite.  This is used for any subsequent
   pread/pwrite.  Thus the current file position of the "normal" file
   handle is not touched.

   FIXME:

   Note that this is just a hack.  The problem with this approach is that
   a change to the file permissions might disallow to open the file with
   the required permissions to read or write.  This appears to be a border case,
   but that's exactly what git does.  It creates the file for reading and
   writing and after writing it, it chmods the file to read-only.  Then it
   calls pread on the file to examine the content.  This works, but if git
   would use the original handle to pwrite to the file, it would be broken
   with our approach.

   One way to implement this is to open the pread/pwrite handle right at
   file open time.  We would simply maintain two handles, which wouldn't
   be much of a problem given how we do that for other fhandler types as
   well.

   However, ultimately fhandler_disk_file should become a derived class of
   fhandler_base_overlapped.  Each raw_read or raw_write would fetch the
   actual file position, read/write from there, and then set the file
   position again.  Fortunately, while the file position is not maintained
   by the I/O manager, it can be fetched and set to a new value by all
   processes holding a handle to that file object.  Pread and pwrite differ
   from raw_read and raw_write just by not touching the current file pos.
   Actually they could be merged with raw_read/raw_write if we add a position
   parameter to the latter. */

int
fhandler_disk_file::prw_open (bool write, void *aio)
{
  NTSTATUS status;
  IO_STATUS_BLOCK io;
  OBJECT_ATTRIBUTES attr;
  ULONG options = get_options ();

  /* If async i/o is intended, turn off the default synchronous operation */
  if (aio)
    options &= ~FILE_SYNCHRONOUS_IO_NONALERT;

  /* First try to open with the original access mask */
  ACCESS_MASK access = get_access ();
  status = NtOpenFile (&prw_handle, access,
		       pc.init_reopen_attr (attr, get_handle ()), &io,
		       FILE_SHARE_VALID_FLAGS, options);
  if (status == STATUS_ACCESS_DENIED)
    {
      /* If we get an access denied, chmod has been called.  Try again
	 with just the required rights to perform the called function. */
      access &= write ? ~GENERIC_READ : ~GENERIC_WRITE;
      status = NtOpenFile (&prw_handle, access, &attr, &io,
			   FILE_SHARE_VALID_FLAGS, options);
    }
  debug_printf ("%y = NtOpenFile (%p, %y, %S, io, %y, %y)",
		status, prw_handle, access, pc.get_nt_native_path (),
		FILE_SHARE_VALID_FLAGS, options);
  if (!NT_SUCCESS (status))
    {
      __seterrno_from_nt_status (status);
      return -1;
    }

  /* record prw_handle's asyncness for subsequent pread/pwrite operations */
  prw_handle_isasync = !!aio;
  return 0;
}

ssize_t
fhandler_disk_file::pread (void *buf, size_t count, off_t offset, void *aio)
{
  struct aiocb *aiocb = (struct aiocb *) aio;
  ssize_t res;

  if ((get_flags () & O_ACCMODE) == O_WRONLY)
    {
      set_errno (EBADF);
      return -1;
    }

  /* In binary mode, we can use an atomic NtReadFile call.
     Windows mandatory locking semantics disallow to use another HANDLE. */
  if (rbinary () && !mandatory_locking ())
    {
      extern int is_at_eof (HANDLE h);
      NTSTATUS status;
      IO_STATUS_BLOCK io;
      LARGE_INTEGER off = { QuadPart:offset };
      HANDLE evt = aio ? (HANDLE) aiocb->aio_wincb.event : NULL;
      PIO_STATUS_BLOCK pio = aio ? (PIO_STATUS_BLOCK) &aiocb->aio_wincb : &io;

      /* If existing prw_handle asyncness doesn't match this call's, re-open */
      if (prw_handle && (prw_handle_isasync != !!aio))
	NtClose (prw_handle), prw_handle = NULL;

      if (!prw_handle && prw_open (false, aio))
	goto non_atomic;
      status = NtReadFile (prw_handle, evt, NULL, NULL, pio, buf, count,
			   &off, NULL);
      if (status == STATUS_END_OF_FILE)
	res = 0;
      else if (!NT_SUCCESS (status))
	{
	  if (pc.isdir ())
	    {
	      set_errno (EISDIR);
	      return -1;
	    }
	  if (status == (NTSTATUS) STATUS_ACCESS_VIOLATION)
	    {
	      if (is_at_eof (prw_handle))
		{
		  res = 0;
		  goto out;
		}
	      switch (mmap_is_attached_or_noreserve (buf, count))
		{
		case MMAP_NORESERVE_COMMITED:
                  status = NtReadFile (prw_handle, evt, NULL, NULL, pio,
				       buf, count, &off, NULL);
		  if (NT_SUCCESS (status))
		    {
		      res = aio ? (ssize_t) aiocb->aio_wincb.info
                                : io.Information;
		      goto out;
		    }
		  break;
		case MMAP_RAISE_SIGBUS:
		  raise (SIGBUS);
		default:
		  break;
		}
	    }
	  __seterrno_from_nt_status (status);
	  return -1;
	}
      else
	{
	  res = aio ? (ssize_t) aiocb->aio_wincb.info : io.Information;
	  goto out;
	}
    }
  else
    {
non_atomic:
      /* Text mode stays slow and non-atomic. */
      off_t curpos = lseek (0, SEEK_CUR);
      if (curpos < 0 || lseek (offset, SEEK_SET) < 0)
	res = -1;
      else
	{
	  size_t tmp_count = count;
	  read (buf, tmp_count);
	  if (lseek (curpos, SEEK_SET) >= 0)
	    res = (ssize_t) tmp_count;
	  else
	    res = -1;
	}

      /* If this was a disallowed async request, simulate its conclusion */
      if (aio)
	{
	  aiocb->aio_rbytes = res;
	  aiocb->aio_errno = res == -1 ? get_errno () : 0;
	  SetEvent ((HANDLE) aiocb->aio_wincb.event);
	}
    }
out:
  debug_printf ("%d = pread(%p, %ld, %D, %p)\n", res, buf, count, offset, aio);
  return res;
}

ssize_t
fhandler_disk_file::pwrite (void *buf, size_t count, off_t offset, void *aio)
{
  struct aiocb *aiocb = (struct aiocb *) aio;
  ssize_t res;

  if ((get_flags () & O_ACCMODE) == O_RDONLY)
    {
      set_errno (EBADF);
      return -1;
    }

  /* In binary mode, we can use an atomic NtWriteFile call.
     Windows mandatory locking semantics disallow to use another HANDLE. */
  if (wbinary () && !mandatory_locking ())
    {
      NTSTATUS status;
      IO_STATUS_BLOCK io;
      LARGE_INTEGER off = { QuadPart:offset };
      HANDLE evt = aio ? (HANDLE) aiocb->aio_wincb.event : NULL;
      PIO_STATUS_BLOCK pio = aio ? (PIO_STATUS_BLOCK) &aiocb->aio_wincb : &io;

      /* If existing prw_handle asyncness doesn't match this call's, re-open */
      if (prw_handle && (prw_handle_isasync != !!aio))
        NtClose (prw_handle), prw_handle = NULL;

      if (!prw_handle && prw_open (true, aio))
	goto non_atomic;
      status = NtWriteFile (prw_handle, evt, NULL, NULL, pio, buf, count,
			    &off, NULL);
      if (!NT_SUCCESS (status))
	{
	  __seterrno_from_nt_status (status);
	  return -1;
	}
      res = aio ? (ssize_t) aiocb->aio_wincb.info : io.Information;
      goto out;
    }
  else
    {
non_atomic:
      /* Text mode stays slow and non-atomic. */
      off_t curpos = lseek (0, SEEK_CUR);
      if (curpos < 0 || lseek (offset, SEEK_SET) < 0)
	res = curpos;
      else
	{
	  res = (ssize_t) write (buf, count);
	  if (lseek (curpos, SEEK_SET) < 0)
	    res = -1;
	}

      /* If this was a disallowed async request, simulate its conclusion */
      if (aio)
	{
	  aiocb->aio_rbytes = res;
	  aiocb->aio_errno = res == -1 ? get_errno () : 0;
	  SetEvent ((HANDLE) aiocb->aio_wincb.event);
	}
    }
out:
  debug_printf ("%d = pwrite(%p, %ld, %D, %p)\n", res, buf, count, offset, aio);
  return res;
}

int
fhandler_disk_file::mkdir (mode_t mode)
{
  int res = -1;
  SECURITY_ATTRIBUTES sa = sec_none_nih;
  NTSTATUS status;
  HANDLE dir;
  OBJECT_ATTRIBUTES attr;
  IO_STATUS_BLOCK io;
  PFILE_FULL_EA_INFORMATION p = NULL;
  ULONG plen = 0;
  ULONG access = FILE_LIST_DIRECTORY | SYNCHRONIZE;

  if (pc.fs_is_nfs ())
    {
      /* When creating a dir on an NFS share, we have to set the
	 file mode by writing a NFS fattr3 structure with the
	 correct mode bits set. */
      plen = sizeof (FILE_FULL_EA_INFORMATION) + sizeof (NFS_V3_ATTR)
	     + sizeof (fattr3);
      p = (PFILE_FULL_EA_INFORMATION) alloca (plen);
      p->NextEntryOffset = 0;
      p->Flags = 0;
      p->EaNameLength = sizeof (NFS_V3_ATTR) - 1;
      p->EaValueLength = sizeof (fattr3);
      strcpy (p->EaName, NFS_V3_ATTR);
      fattr3 *nfs_attr = (fattr3 *) (p->EaName + p->EaNameLength + 1);
      memset (nfs_attr, 0, sizeof (fattr3));
      nfs_attr->type = NF3DIR;
      nfs_attr->mode = (mode & 07777) & ~cygheap->umask;
    }
  else if (has_acls () && !isremote ())
    /* If the filesystem supports ACLs, we will overwrite the DACL after the
       call to NtCreateFile.  This requires a handle with READ_CONTROL and
       WRITE_DAC access, otherwise get_file_sd and set_file_sd both have to
       open the file again.
       FIXME: On remote NTFS shares open sometimes fails because even the
       creator of the file doesn't have the right to change the DACL.
       I don't know what setting that is or how to recognize such a share,
       so for now we don't request WRITE_DAC on remote drives. */
    access |= READ_CONTROL | WRITE_DAC;
  /* Setting case sensitivity requires FILE_WRITE_ATTRIBUTES. */
  if (wincap.has_case_sensitive_dirs ()
      && !pc.isremote () && pc.fs_is_ntfs ())
    access |= FILE_WRITE_ATTRIBUTES;
  status = NtCreateFile (&dir, access, pc.get_object_attr (attr, sa), &io, NULL,
			 FILE_ATTRIBUTE_DIRECTORY, FILE_SHARE_VALID_FLAGS,
			 FILE_CREATE,
			 FILE_DIRECTORY_FILE | FILE_SYNCHRONOUS_IO_NONALERT
			 | FILE_OPEN_FOR_BACKUP_INTENT,
			 p, plen);
  if (NT_SUCCESS (status))
    {
      /* Set the "directory attribute" so that pc.isdir() returns correct
	 value in subsequent function calls. */
      pc.file_attributes (FILE_ATTRIBUTE_DIRECTORY);
      if (has_acls ())
	set_created_file_access (dir, pc, mode & 07777);
#if 0
      /* FIXME: This default behaviour badly breaks interoperability.
		Inspecting the content of case-sensitive directories
		on remote machines results in lots of errors like
		disappearing diretories and files, file not found, etc. */

      /* Starting with Windows 10 1803, try to create all dirs below the
         installation root as case-sensitive.  If STATUS_NOT_SUPPORTED
	 is returned, WSL isn't installed (unfortunately a requirement
	 for this functionality. */
      if (wincap.has_case_sensitive_dirs ()
	  && !pc.isremote () && pc.fs_is_ntfs ())
	{
	  PUNICODE_STRING new_dir = pc.get_nt_native_path ();
	  PUNICODE_STRING root_dir = &cygheap->installation_root;

	  if (RtlEqualUnicodePathPrefix (new_dir, root_dir, TRUE)
	      && new_dir->Buffer[root_dir->Length / sizeof (WCHAR)] == L'\\')
	    {
	      FILE_CASE_SENSITIVE_INFORMATION fcsi;

	      fcsi.Flags = FILE_CS_FLAG_CASE_SENSITIVE_DIR;
	      status = NtSetInformationFile (dir, &io, &fcsi, sizeof fcsi,
					     FileCaseSensitiveInformation);
	      if (!NT_SUCCESS (status))
		{
		  debug_printf ("Setting dir case sensitivity, status %y",
				status);
		  if (status == STATUS_NOT_SUPPORTED)
		    {
		      debug_printf ("Dir case sensitivity requires WSL");
		      wincap.disable_case_sensitive_dirs ();
		    }
		}
	    }
	}
#endif
      NtClose (dir);
      res = 0;
    }
  else
    __seterrno_from_nt_status (status);

  return res;
}

int
fhandler_disk_file::rmdir ()
{
  extern NTSTATUS unlink_nt (path_conv &pc);

  if (!pc.isdir ())
    {
      set_errno (ENOTDIR);
      return -1;
    }
  if (!pc.exists ())
    {
      set_errno (ENOENT);
      return -1;
    }

  NTSTATUS status = unlink_nt (pc);

  if (!NT_SUCCESS (status))
    {
      __seterrno_from_nt_status (status);
      return -1;
    }
  return 0;
}

/* This is the minimal number of entries which fit into the readdir cache.
   The number of bytes allocated by the cache is determined by this number,
   To tune caching, just tweak this number.  To get a feeling for the size,
   the size of the readdir cache is DIR_NUM_ENTRIES * 624 + 4 bytes.  */

#define DIR_NUM_ENTRIES	100		/* Cache size 62404 bytes */

#define DIR_BUF_SIZE	(DIR_NUM_ENTRIES \
			 * (sizeof (FILE_ID_BOTH_DIR_INFORMATION) \
			    + (NAME_MAX + 1) * sizeof (WCHAR)))

struct __DIR_cache
{
  char  __cache[DIR_BUF_SIZE];
  ULONG __pos;
};

#define d_cachepos(d)	(((__DIR_cache *) (d)->__d_dirname)->__pos)
#define d_cache(d)	(((__DIR_cache *) (d)->__d_dirname)->__cache)

#define d_mounts(d)	((__DIR_mounts *) (d)->__d_internal)

DIR *
fhandler_disk_file::opendir (int fd)
{
  DIR *dir;
  DIR *res = NULL;

  if (!pc.isdir ())
    set_errno (ENOTDIR);
  else if ((dir = (DIR *) malloc (sizeof (DIR))) == NULL)
    set_errno (ENOMEM);
  else if ((dir->__d_dirname = (char *) malloc ( sizeof (struct __DIR_cache)))
	   == NULL)
    {
      set_errno (ENOMEM);
      goto free_dir;
    }
  else if ((dir->__d_dirent =
	    (struct dirent *) malloc (sizeof (struct dirent))) == NULL)
    {
      set_errno (ENOMEM);
      goto free_dirname;
    }
  else
    {
      cygheap_fdnew cfd;
      if (cfd < 0 && fd < 0)
	goto free_dirent;

      dir->__d_dirent->__d_version = __DIRENT_VERSION;
      dir->__d_cookie = __DIRENT_COOKIE;
      dir->__handle = INVALID_HANDLE_VALUE;
      dir->__d_position = 0;
      dir->__flags = (get_name ()[0] == '/' && get_name ()[1] == '\0')
		     ? dirent_isroot : 0;
      dir->__d_internal = 0;

      if (pc.iscygdrive ())
	{
	  if (fd < 0 && !open (O_RDONLY, 0))
	    goto free_mounts;
	}
      else
	{
	  dir->__d_internal = (uintptr_t) new __DIR_mounts (get_name ());
	  d_cachepos (dir) = 0;
	  if (fd < 0)
	    {
	      /* opendir() case.  Initialize with given directory name and
		 NULL directory handle. */
	      OBJECT_ATTRIBUTES attr;
	      NTSTATUS status;
	      IO_STATUS_BLOCK io;
	      /* Tools like ls(1) call dirfd() to fetch the directory
		 descriptor for calls to facl or fstat.  The tight access mask
		 used so far is not sufficient to reuse the handle for these
		 calls, instead the facl/fstat calls find the handle to be
		 unusable and have to re-open the file for reading attributes
		 and control data.  So, what we do here is to try to open the
		 directory with more relaxed access mask which enables to use
		 the handle for the aforementioned purpose.  This should work
		 in almost all cases.  Only if it doesn't work due to
		 permission problems, we drop the additional access bits and
		 try again. */
	      ACCESS_MASK fstat_mask = READ_CONTROL | FILE_READ_ATTRIBUTES;

	      do
		{
		  status = NtOpenFile (&get_handle (),
				       SYNCHRONIZE | FILE_LIST_DIRECTORY
				       | fstat_mask,
				       pc.get_object_attr (attr, sec_none_nih),
				       &io, FILE_SHARE_VALID_FLAGS,
				       FILE_SYNCHRONOUS_IO_NONALERT
				       | FILE_OPEN_FOR_BACKUP_INTENT
				       | FILE_DIRECTORY_FILE);
		  if (!NT_SUCCESS (status))
		    {
		      if (status == STATUS_ACCESS_DENIED && fstat_mask)
			fstat_mask = 0;
		      else
			{
			  __seterrno_from_nt_status (status);
			  goto free_mounts;
			}
		    }
		}
	      while (!NT_SUCCESS (status));
	    }

	  /* FileIdBothDirectoryInformation was unsupported on XP when
	     accessing UDF.  It's not clear if the call isn't also unsupported
	     on other OS/FS combinations.  Instead of testing for yet another
	     error code, use FileIdBothDirectoryInformation only on FSes
	     supporting persistent ACLs.

	     NFS clients hide dangling symlinks from directory queries,
	     unless you use the FileNamesInformation info class.
	     FileIdBothDirectoryInformation works fine, but only if the NFS
	     share is mounted to a drive letter.  TODO: We don't test that
	     here for now, but it might be worth to test if there's a speed
	     gain in using FileIdBothDirectoryInformation, because it doesn't
	     require to open the file to read the inode number. */
	  if (pc.hasgood_inode ())
	    {
	      dir->__flags |= dirent_set_d_ino;
	      if (pc.fs_is_nfs ())
		dir->__flags |= dirent_nfs_d_ino;
	      else if (!pc.has_buggy_fileid_dirinfo ())
		dir->__flags |= dirent_get_d_ino;
	    }
	}
      if (fd >= 0)
	dir->__d_fd = fd;
      else
	{
	  /* Filling cfd with `this' (aka storing this in the file
	     descriptor table should only happen after it's clear that
	     opendir doesn't fail, otherwise we end up cfree'ing the
	     fhandler twice, once in opendir() in dir.cc, the second
	     time on exit.  Nasty, nasty... */
	  cfd = this;
	  dir->__d_fd = cfd;
	}
      set_close_on_exec (true);
      dir->__fh = this;
      res = dir;
    }

  syscall_printf ("%p = opendir (%s)", res, get_name ());
  return res;

free_mounts:
  delete d_mounts (dir);
free_dirent:
  free (dir->__d_dirent);
free_dirname:
  free (dir->__d_dirname);
free_dir:
  free (dir);
  return res;
}

ino_t
readdir_get_ino (const char *path, bool dot_dot)
{
  char *fname;
  struct stat st;
  HANDLE hdl;
  OBJECT_ATTRIBUTES attr;
  IO_STATUS_BLOCK io;
  ino_t ino = 0;

  if (dot_dot)
    {
      fname = (char *) alloca (strlen (path) + 4);
      char *c = stpcpy (fname, path);
      if (c[-1] != '/')
	*c++ = '/';
      strcpy (c, "..");
      path = fname;
    }
  path_conv pc (path, PC_SYM_NOFOLLOW | PC_POSIX | PC_KEEP_HANDLE);
  if (pc.isspecial ())
    {
      if (!stat_worker (pc, &st))
	ino = st.st_ino;
    }
  else if (!pc.hasgood_inode ())
    ino = hash_path_name (0, pc.get_nt_native_path ());
  else if ((hdl = pc.handle ()) != NULL
	   || NT_SUCCESS (NtOpenFile (&hdl, READ_CONTROL,
				      pc.get_object_attr (attr, sec_none_nih),
				      &io, FILE_SHARE_VALID_FLAGS,
				      FILE_OPEN_FOR_BACKUP_INTENT
				      | (pc.is_known_reparse_point ()
				      ? FILE_OPEN_REPARSE_POINT : 0)))
	  )
    {
      ino = pc.get_ino_by_handle (hdl);
      if (!ino)
	ino = hash_path_name (0, pc.get_nt_native_path ());
    }
  return ino;
}

int
fhandler_disk_file::readdir_helper (DIR *dir, dirent *de, DWORD w32_err,
				    DWORD attr, PUNICODE_STRING fname)
{
  if (w32_err)
    {
      switch (d_mounts (dir)->check_missing_mount (fname))
	{
	case __DIR_mount_none:
	  fname->Length = 0;
	  return geterrno_from_win_error (w32_err);
	case __DIR_mount_virt_target:
	  de->d_type = DT_DIR;
	  break;
	default:
	  break;
	}
      attr = 0;
      dir->__flags &= ~dirent_set_d_ino;
    }

  /* Set d_type if type can be determined from file attributes.  For .lnk
     symlinks, d_type will be reset below.  Reparse points can be NTFS
     symlinks, even if they have the FILE_ATTRIBUTE_DIRECTORY flag set. */
  if (attr && !(attr & ~FILE_ATTRIBUTE_VALID_FLAGS))
    {
      if (attr & FILE_ATTRIBUTE_DIRECTORY)
	de->d_type = DT_DIR;
      /* FILE_ATTRIBUTE_SYSTEM might denote system-bit type symlinks. */
      else if (!(attr & FILE_ATTRIBUTE_SYSTEM))
	de->d_type = DT_REG;
    }

  /* Check for reparse points that can be treated as posix symlinks.
     Mountpoints and unknown or unhandled reparse points will be treated
     as normal file/directory/unknown. In all cases, returning the INO of
     the reparse point (not of the target) matches behavior of posix systems.
     */
  if (attr & FILE_ATTRIBUTE_REPARSE_POINT)
    {
      OBJECT_ATTRIBUTES oattr;

      InitializeObjectAttributes (&oattr, fname, pc.objcaseinsensitive (),
				  get_handle (), NULL);
      if (readdir_check_reparse_point (&oattr, isremote ()))
        de->d_type = DT_LNK;
    }

  /* Check for Windows shortcut. If it's a Cygwin or U/WIN symlink, drop the
     .lnk suffix and set d_type accordingly. */
  if ((attr & (FILE_ATTRIBUTE_DIRECTORY
	       | FILE_ATTRIBUTE_REPARSE_POINT
	       | FILE_ATTRIBUTE_READONLY)) == FILE_ATTRIBUTE_READONLY
      && fname->Length > 4 * sizeof (WCHAR))
    {
      UNICODE_STRING uname;

      RtlInitCountedUnicodeString (&uname,
				   fname->Buffer
				   + fname->Length / sizeof (WCHAR) - 4,
				   4 * sizeof (WCHAR));
      if (RtlEqualUnicodeString (&uname, &ro_u_lnk, TRUE))
	{
	  tmp_pathbuf tp;
	  char *file = tp.c_get ();
	  char *p = stpcpy (file, pc.get_posix ());
	  if (p[-1] != '/')
	    *p++ = '/';
	  sys_wcstombs (p, NT_MAX_PATH - (p - file),
			fname->Buffer, fname->Length / sizeof (WCHAR));
	  path_conv fpath (file, PC_SYM_NOFOLLOW);
	  if (fpath.issymlink ())
	    {
	      fname->Length -= 4 * sizeof (WCHAR);
	      de->d_type = DT_LNK;
	    }
	  else if (fpath.isfifo ())
	    {
	      fname->Length -= 4 * sizeof (WCHAR);
	      de->d_type = DT_FIFO;
	    }
	  else if (fpath.is_fs_special ())
	    {
	      fname->Length -= 4 * sizeof (WCHAR);
	      de->d_type = S_ISCHR (fpath.dev.mode ()) ? DT_CHR : DT_BLK;
	    }
	}
    }

  sys_wcstombs (de->d_name, NAME_MAX + 1, fname->Buffer,
		fname->Length / sizeof (WCHAR));

  /* Don't try to optimize relative to dir->__d_position.  On several
     filesystems it's no safe bet that "." and ".." entries always
     come first. */
  if (de->d_name[0] == '.')
    {
      if (de->d_name[1] == '\0')
	dir->__flags |= dirent_saw_dot;
      else if (de->d_name[1] == '.' && de->d_name[2] == '\0')
	dir->__flags |= dirent_saw_dot_dot;
    }
  return 0;
}

int
fhandler_disk_file::readdir (DIR *dir, dirent *de)
{
  int res = 0;
  NTSTATUS status = STATUS_SUCCESS;
  PFILE_ID_BOTH_DIR_INFORMATION buf = NULL;
  PWCHAR FileName;
  ULONG FileNameLength;
  ULONG FileAttributes;
  IO_STATUS_BLOCK io;
  UNICODE_STRING fname;

  /* d_cachepos always refers to the next cache entry to use.  If it's 0
     we must reload the cache. */
  FileAttributes = 0;
  if (d_cachepos (dir) == 0)
    {
      if ((dir->__flags & dirent_get_d_ino))
	{
	  status = NtQueryDirectoryFile (get_handle (), NULL, NULL, NULL, &io,
					 d_cache (dir), DIR_BUF_SIZE,
					 FileIdBothDirectoryInformation,
					 FALSE, NULL, dir->__d_position == 0);
	  /* FileIdBothDirectoryInformation isn't supported for remote drives
	     on NT4 and 2K systems.  There are also hacked versions of
	     Samba 3.0.x out there (Debian-based it seems), which return
	     STATUS_NOT_SUPPORTED rather than handling this info class.
	     We just fall back to using a standard directory query in
	     this case and note this case using the dirent_get_d_ino flag. */
	  if (!NT_SUCCESS (status) && status != STATUS_NO_MORE_FILES
	      && (status == STATUS_INVALID_LEVEL
		  || status == STATUS_NOT_SUPPORTED
		  || status == STATUS_INVALID_PARAMETER
		  || status == STATUS_INVALID_NETWORK_RESPONSE
		  || status == STATUS_INVALID_INFO_CLASS))
	    dir->__flags &= ~dirent_get_d_ino;
	  /* Something weird happens on Samba up to version 3.0.21c, which is
	     fixed in 3.0.22.  FileIdBothDirectoryInformation seems to work
	     nicely, but only up to the 128th entry in the directory.  After
	     reaching this entry, the next call to NtQueryDirectoryFile
	     (FileIdBothDirectoryInformation) returns STATUS_INVALID_LEVEL.
	     Why should we care, we can just switch to
	     FileBothDirectoryInformation, isn't it?  Nope!  The next call to
	     NtQueryDirectoryFile(FileBothDirectoryInformation) actually
	     returns STATUS_NO_MORE_FILES, regardless how many files are left
	     unread in the directory.  This does not happen when using
	     FileBothDirectoryInformation right from the start, but since
	     we can't decide whether the server we're talking with has this
	     bug or not, we end up serving Samba shares always in the slow
	     mode using FileBothDirectoryInformation.  So, what we do here is
	     to implement the solution suggested by Andrew Tridgell,  we just
	     reread all entries up to dir->d_position using
	     FileBothDirectoryInformation.
	     However, We do *not* mark this server as broken and fall back to
	     using FileBothDirectoryInformation further on.  This would slow
	     down every access to such a server, even for directories under
	     128 entries.  Also, bigger dirs only suffer from one additional
	     call per full directory scan, which shouldn't be too big a hit.
	     This can easily be changed if necessary. */
	  if (status == STATUS_INVALID_LEVEL && dir->__d_position)
	    {
	      d_cachepos (dir) = 0;
	      for (int cnt = 0; cnt < dir->__d_position; ++cnt)
		{
		  if (d_cachepos (dir) == 0)
		    {
		      status = NtQueryDirectoryFile (get_handle (), NULL, NULL,
					   NULL, &io, d_cache (dir),
					   DIR_BUF_SIZE,
					   FileBothDirectoryInformation,
					   FALSE, NULL, cnt == 0);
		      if (!NT_SUCCESS (status))
			goto go_ahead;
		    }
		  buf = (PFILE_ID_BOTH_DIR_INFORMATION) (d_cache (dir)
							 + d_cachepos (dir));
		  if (buf->NextEntryOffset == 0)
		    d_cachepos (dir) = 0;
		  else
		    d_cachepos (dir) += buf->NextEntryOffset;
		}
	      goto go_ahead;
	    }
	}
      if (!(dir->__flags & dirent_get_d_ino))
	status = NtQueryDirectoryFile (get_handle (), NULL, NULL, NULL, &io,
				       d_cache (dir), DIR_BUF_SIZE,
				       (dir->__flags & dirent_nfs_d_ino)
				       ? FileNamesInformation
				       : FileBothDirectoryInformation,
				       FALSE, NULL, dir->__d_position == 0);
    }

go_ahead:

  if (status == STATUS_NO_MORE_FILES)
    /*nothing*/;
  else if (!NT_SUCCESS (status))
    debug_printf ("NtQueryDirectoryFile failed, status %y, win32 error %u",
		  status, RtlNtStatusToDosError (status));
  else
    {
      buf = (PFILE_ID_BOTH_DIR_INFORMATION) (d_cache (dir) + d_cachepos (dir));
      if (buf->NextEntryOffset == 0)
	d_cachepos (dir) = 0;
      else
	d_cachepos (dir) += buf->NextEntryOffset;
      if ((dir->__flags & dirent_get_d_ino))
	{
	  FileName = buf->FileName;
	  FileNameLength = buf->FileNameLength;
	  FileAttributes = buf->FileAttributes;
	  if ((dir->__flags & dirent_set_d_ino))
	    de->d_ino = buf->FileId.QuadPart;
	}
      else if ((dir->__flags & dirent_nfs_d_ino))
	{
	  FileName = ((PFILE_NAMES_INFORMATION) buf)->FileName;
	  FileNameLength = ((PFILE_NAMES_INFORMATION) buf)->FileNameLength;
	}
      else
	{
	  FileName = ((PFILE_BOTH_DIR_INFORMATION) buf)->FileName;
	  FileNameLength =
		((PFILE_BOTH_DIR_INFORMATION) buf)->FileNameLength;
	  FileAttributes =
		((PFILE_BOTH_DIR_INFORMATION) buf)->FileAttributes;
	}
      RtlInitCountedUnicodeString (&fname, FileName, FileNameLength);
      d_mounts (dir)->check_mount (&fname);
      if (de->d_ino == 0 && (dir->__flags & dirent_set_d_ino))
	{
	  /* Don't try to optimize relative to dir->__d_position.  On several
	     filesystems it's no safe bet that "." and ".." entries always
	     come first. */
	  if (FileNameLength == sizeof (WCHAR) && FileName[0] == '.')
	    de->d_ino = pc.get_ino_by_handle (get_handle ());
	  else if (FileNameLength == 2 * sizeof (WCHAR)
		   && FileName[0] == L'.' && FileName[1] == L'.')
	    {
	      if (!(dir->__flags & dirent_isroot))
		de->d_ino = readdir_get_ino (get_name (), true);
	      else
		de->d_ino = pc.get_ino_by_handle (get_handle ());
	    }
	  else
	    {
	      OBJECT_ATTRIBUTES attr;
	      HANDLE hdl;
	      NTSTATUS f_status;

	      InitializeObjectAttributes (&attr, &fname,
					  pc.objcaseinsensitive (),
					  get_handle (), NULL);
	      /* FILE_OPEN_REPARSE_POINT on NFS is a no-op, so the normal
		 NtOpenFile here returns the inode number of the symlink target,
		 rather than the inode number of the symlink itself.

		 Worse, trying to open a symlink without setting the special
		 "ActOnSymlink" EA triggers a bug in Windows 7 which results
		 in a timeout of up to 20 seconds, followed by two exceptions
		 in the NT kernel.

		 Since both results are far from desirable, we open symlinks
		 on NFS so that we get the right inode and a happy W7.
		 And, since some filesystems choke on the EAs, we don't
		 use them unconditionally. */
	      f_status = (dir->__flags & dirent_nfs_d_ino)
			 ? NtCreateFile (&hdl, READ_CONTROL, &attr, &io,
					 NULL, 0, FILE_SHARE_VALID_FLAGS,
					 FILE_OPEN, FILE_OPEN_FOR_BACKUP_INTENT,
					 &nfs_aol_ffei, sizeof nfs_aol_ffei)
			 : NtOpenFile (&hdl, READ_CONTROL, &attr, &io,
				       FILE_SHARE_VALID_FLAGS,
				       FILE_OPEN_FOR_BACKUP_INTENT
				       | FILE_OPEN_REPARSE_POINT);
	      if (NT_SUCCESS (f_status))
		{
		  /* We call NtQueryInformationFile here, rather than
		     pc.get_ino_by_handle(), otherwise we can't short-circuit
		     dirent_set_d_ino correctly. */
		  FILE_INTERNAL_INFORMATION fii;
		  f_status = NtQueryInformationFile (hdl, &io, &fii, sizeof fii,
						     FileInternalInformation);
		  NtClose (hdl);
		  if (NT_SUCCESS (f_status))
		    {
		      if (pc.isgood_inode (fii.IndexNumber.QuadPart))
			de->d_ino = fii.IndexNumber.QuadPart;
		      else
			/* Untrusted file system.  Don't try to fetch inode
			   number again. */
			dir->__flags &= ~dirent_set_d_ino;
		    }
		}
	    }
	}
    }

  if (!(res = readdir_helper (dir, de, RtlNtStatusToDosError (status),
			      FileAttributes, &fname)))
    dir->__d_position++;
  else if (!(dir->__flags & dirent_saw_dot))
    {
      strcpy (de->d_name , ".");
      de->d_ino = pc.get_ino_by_handle (get_handle ());
      de->d_type = DT_DIR;
      dir->__d_position++;
      dir->__flags |= dirent_saw_dot;
      res = 0;
    }
  else if (!(dir->__flags & dirent_saw_dot_dot))
    {
      strcpy (de->d_name , "..");
      if (!(dir->__flags & dirent_isroot))
	de->d_ino = readdir_get_ino (get_name (), true);
      else
	de->d_ino = pc.get_ino_by_handle (get_handle ());
      de->d_type = DT_DIR;
      dir->__d_position++;
      dir->__flags |= dirent_saw_dot_dot;
      res = 0;
    }

  syscall_printf ("%d = readdir(%p, %p) (L\"%lS\" > \"%ls\") (attr %y > type %d)",
		  res, dir, &de, res ? NULL : &fname, res ? "***" : de->d_name,
		  FileAttributes, de->d_type);
  return res;
}

long
fhandler_disk_file::telldir (DIR *dir)
{
  return dir->__d_position;
}

void
fhandler_disk_file::seekdir (DIR *dir, long loc)
{
  rewinddir (dir);
  while (loc > dir->__d_position)
    if (!::readdir (dir))
      break;
}

void
fhandler_disk_file::rewinddir (DIR *dir)
{
  d_cachepos (dir) = 0;
  dir->__d_position = 0;
  d_mounts (dir)->rewind ();
}

int
fhandler_disk_file::closedir (DIR *dir)
{
  int res = 0;

  delete d_mounts (dir);
  syscall_printf ("%d = closedir(%p, %s)", res, dir, get_name ());
  return res;
}

uint64_t
fhandler_disk_file::fs_ioc_getflags ()
{
  NTSTATUS status;
  IO_STATUS_BLOCK io;
  FILE_BASIC_INFORMATION fbi;
  FILE_CASE_SENSITIVE_INFORMATION fcsi;
  uint64_t flags = 0;

  status = NtQueryInformationFile (get_handle (), &io, &fbi, sizeof fbi,
				   FileBasicInformation);
  if (NT_SUCCESS (status))
    {
      flags = (uint64_t) fbi.FileAttributes & FS_FL_USER_VISIBLE;
      pc.file_attributes (fbi.FileAttributes);
    }
  else
    flags = (uint64_t) pc.file_attributes () & FS_FL_USER_VISIBLE;
  if (pc.isdir () && wincap.has_case_sensitive_dirs ()
      && !pc.isremote () && pc.fs_is_ntfs ())
    {
      fcsi.Flags = 0;
      status = NtQueryInformationFile (get_handle (), &io,
				       &fcsi, sizeof fcsi,
				       FileCaseSensitiveInformation);
      if (NT_SUCCESS (status)
	  && (fcsi.Flags & FILE_CS_FLAG_CASE_SENSITIVE_DIR))
	flags |= FS_CASESENS_FL;
    }
  return flags;
}

/* Settable DOS attributes */
#define FS_FL_SETATTRIBS	(FS_READONLY_FL \
				 | FS_HIDDEN_FL \
				 | FS_SYSTEM_FL \
				 | FS_ARCHIVE_FL \
				 | FS_TEMP_FL \
				 | FS_NOTINDEXED_FL)

int
fhandler_disk_file::fs_ioc_setflags (uint64_t flags)
{
  int ret = -1;
  uint64_t old_flags;
  HANDLE fh;
  NTSTATUS status;
  OBJECT_ATTRIBUTES attr;
  IO_STATUS_BLOCK io;
  FILE_BASIC_INFORMATION fbi;
  FILE_SET_SPARSE_BUFFER fssb;
  USHORT comp;
  FILE_CASE_SENSITIVE_INFORMATION fcsi;

  if ((get_access () & (GENERIC_WRITE | FILE_WRITE_ATTRIBUTES)) != 0)
    fh = get_handle ();
  else
    {
      status = NtOpenFile (&fh, FILE_READ_ATTRIBUTES | FILE_WRITE_ATTRIBUTES,
			   pc.init_reopen_attr (attr, get_handle ()), &io,
			   FILE_SHARE_VALID_FLAGS,
			   FILE_OPEN_FOR_BACKUP_INTENT);
      if (!NT_SUCCESS (status))
	{
	  fh = get_handle ();
	  __seterrno_from_nt_status (status);
	  goto out;
	}
    }
  old_flags = fs_ioc_getflags ();
  if ((old_flags & FS_FL_SETATTRIBS) != (flags & FS_FL_SETATTRIBS))
    {
      fbi.CreationTime.QuadPart
      = fbi.LastAccessTime.QuadPart
      = fbi.LastWriteTime.QuadPart
      = fbi.ChangeTime.QuadPart = 0LL;
      fbi.FileAttributes = (ULONG) old_flags;
      fbi.FileAttributes &= ~FS_FL_SETATTRIBS;
      fbi.FileAttributes |= (flags & FS_FL_SETATTRIBS);
      if (fbi.FileAttributes == 0)
	fbi.FileAttributes = FILE_ATTRIBUTE_NORMAL;
      status = NtSetInformationFile (fh, &io, &fbi, sizeof fbi,
				     FileBasicInformation);
      if (!NT_SUCCESS (status))
	{
	  __seterrno_from_nt_status (status);
	  goto out;
	}
    }
  if (!pc.isdir() && (flags & FS_SPARSE_FL) != (old_flags & FS_SPARSE_FL))
    {
      fssb.SetSparse = (flags & FS_SPARSE_FL) ? TRUE : FALSE;
      status = NtFsControlFile (fh, NULL, NULL, NULL, &io,
				FSCTL_SET_SPARSE, &fssb, sizeof fssb, NULL, 0);
      if (!NT_SUCCESS (status))
	{
	  __seterrno_from_nt_status (status);
	  goto out;
	}
    }
  if (pc.isdir () && (flags & FS_CASESENS_FL) != (old_flags & FS_CASESENS_FL))
    {
      if (wincap.has_case_sensitive_dirs ()
	  && !pc.isremote () && pc.fs_is_ntfs ())
	{
	  fcsi.Flags = (flags & FS_CASESENS_FL)
		       ? FILE_CS_FLAG_CASE_SENSITIVE_DIR : 0;
	  status = NtSetInformationFile (fh, &io, &fcsi, sizeof fcsi,
					 FileCaseSensitiveInformation);
	  if (!NT_SUCCESS (status))
	    {
	      __seterrno_from_nt_status (status);
	      goto out;
	    }
	}
      else
	{
	  set_errno (ENOTSUP);
	  goto out;
	}
    }
  if ((flags & FS_COMPRESSED_FL) != (old_flags & FS_COMPRESSED_FL))
    {
      if (fh != get_handle ())
	NtClose (fh);
      fh = NULL;
      if ((get_access () & (GENERIC_WRITE | GENERIC_READ))
	  != (GENERIC_WRITE | GENERIC_READ))
	{
	  status = NtOpenFile (&fh, GENERIC_READ | GENERIC_WRITE | SYNCHRONIZE,
			       pc.init_reopen_attr (attr, get_handle ()), &io,
			       FILE_SHARE_VALID_FLAGS,
			       FILE_SYNCHRONOUS_IO_NONALERT
			       | FILE_OPEN_FOR_BACKUP_INTENT);
	  if (!NT_SUCCESS (status))
	    {
	      fh = get_handle ();
	      __seterrno_from_nt_status (status);
	      goto out;
	    }
	}
      comp = (flags & FS_COMPRESSED_FL)
	     ? COMPRESSION_FORMAT_DEFAULT : COMPRESSION_FORMAT_NONE;
      status = NtFsControlFile (fh, NULL, NULL, NULL, &io,
				FSCTL_SET_COMPRESSION, &comp, sizeof comp,
				NULL, 0);
      if (!NT_SUCCESS (status))
	{
	  __seterrno_from_nt_status (status);
	  goto out;
	}
    }
  if (!pc.isdir() && (flags & FS_ENCRYPT_FL) != (old_flags & FS_ENCRYPT_FL))
    {
      tmp_pathbuf tp;
      PWCHAR path = tp.w_get ();
      BOOL cret;

      /* EncryptFileW/DecryptFileW needs exclusive access. */
      if (fh != get_handle ())
	NtClose (fh);
      NtClose (get_handle ());
      set_handle (NULL);

      pc.get_wide_win32_path (path);
      cret = (flags & FS_ENCRYPT_FL)
	     ? EncryptFileW (path) : DecryptFileW (path, 0);
      status = NtOpenFile (&fh, get_access (),
			   pc.get_object_attr (attr, sec_none_nih), &io,
			   FILE_SHARE_VALID_FLAGS,
			   FILE_SYNCHRONOUS_IO_NONALERT
			   | FILE_OPEN_FOR_BACKUP_INTENT);
      if (!NT_SUCCESS (status))
	{
	  __seterrno_from_nt_status (status);
	  return -1;
	}
      set_handle (fh);
      if (!cret)
	{
	  __seterrno ();
	  goto out;
	}
    }
  ret = 0;
out:
  status = NtQueryInformationFile (fh, &io, &fbi, sizeof fbi,
				   FileBasicInformation);
  if (NT_SUCCESS (status))
    pc.file_attributes (fbi.FileAttributes);
  if (fh != get_handle ())
    NtClose (fh);
  return ret;
}

int
fhandler_disk_file::ioctl (unsigned int cmd, void *p)
{
  int ret = -1;
  uint64_t flags = 0;

  switch (cmd)
    {
    case FS_IOC_GETFLAGS:
      __try
	{
	  uint64_t *fp = (uint64_t *) p;
	  *fp = fs_ioc_getflags ();
	  ret = 0;
	}
      __except (EFAULT) {}
      __endtry
      break;
    case FS_IOC_SETFLAGS:
      __try
	{
	  flags = *(__uint64_t *) p;
	}
      __except (EFAULT)
	{
	  break;
	}
      __endtry
      if (flags & ~FS_FL_USER_MODIFIABLE)
	{
	  set_errno (EINVAL);
	  break;
	}
      ret = fs_ioc_setflags (flags);
      break;
    default:
      ret = fhandler_base::ioctl (cmd, p);
      break;
    }
  syscall_printf ("%d = ioctl_file(%x, %p)", ret, cmd, p);
  return ret;
}
