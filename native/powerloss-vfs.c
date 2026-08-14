/*
** Test-only SQLite VFS that models loss of unsynced writes.
**
** This is a small loadable-extension counterpart of src/test6.c for builds
** without the Tcl development headers. Writes are buffered until xSync. At a
** configured sync point, an arbitrary deterministic subset of all outstanding
** writes is sent to the underlying files, synced, and the process exits. Thus
** a journal whose xSync was skipped may be lost while main-file writes survive.
** It is a fault-injection tool, not part of SQLeanite's trusted core.
*/
#include "sqlite3ext.h"
SQLITE_EXTENSION_INIT1

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

typedef struct PowerFile PowerFile;
typedef struct PendingWrite PendingWrite;

struct PendingWrite {
  PowerFile *file;
  sqlite3_int64 offset;
  int amount;                 /* -1 denotes truncate-to-offset. */
  unsigned char *bytes;
  PendingWrite *next;
};

struct PowerFile {
  sqlite3_file base;
  sqlite3_file *real;
  char *name;
};

static sqlite3_vfs powerVfs;
static PendingWrite *pendingHead;
static PendingWrite *pendingTail;
static char *crashFile;
static int crashDelay;
static uint32_t crashRandom = 1;

static sqlite3_vfs *underlying(sqlite3_vfs *vfs){
  return (sqlite3_vfs *)vfs->pAppData;
}

static uint32_t nextRandom(void){
  crashRandom = crashRandom * 1664525u + 1013904223u;
  return crashRandom;
}

static int appendPending(PowerFile *file, const void *bytes, int amount,
                         sqlite3_int64 offset){
  PendingWrite *write = sqlite3_malloc64(sizeof(*write));
  if( write==0 ) return SQLITE_NOMEM;
  memset(write, 0, sizeof(*write));
  write->file = file;
  write->offset = offset;
  write->amount = amount;
  if( amount>0 ){
    write->bytes = sqlite3_malloc64((sqlite3_uint64)amount);
    if( write->bytes==0 ){
      sqlite3_free(write);
      return SQLITE_NOMEM;
    }
    memcpy(write->bytes, bytes, (size_t)amount);
  }
  if( pendingTail ) pendingTail->next = write;
  else pendingHead = write;
  pendingTail = write;
  return SQLITE_OK;
}

static int applyPending(PendingWrite *write){
  if( write->amount<0 ){
    return write->file->real->pMethods->xTruncate(
      write->file->real, write->offset
    );
  }
  return write->file->real->pMethods->xWrite(
    write->file->real, write->bytes, write->amount, write->offset
  );
}

static void freePending(PendingWrite *write){
  sqlite3_free(write->bytes);
  sqlite3_free(write);
}

/* Flush writes through the last pending write for this file. This preserves
** cross-file issue order in the same style as SQLite's crash-test VFS. */
static int flushFile(PowerFile *file){
  PendingWrite *last = 0;
  PendingWrite *cursor;
  PendingWrite **link = &pendingHead;
  int rc = SQLITE_OK;
  for(cursor=pendingHead; cursor; cursor=cursor->next){
    if( cursor->file==file ) last = cursor;
  }
  if( last==0 ) return SQLITE_OK;
  while( *link ){
    PendingWrite *write = *link;
    int final = write==last;
    rc = applyPending(write);
    if( rc!=SQLITE_OK ) return rc;
    *link = write->next;
    if( pendingTail==write ) pendingTail = 0;
    freePending(write);
    if( final ) break;
  }
  if( pendingHead==0 ) pendingTail = 0;
  else if( pendingTail==0 ){
    pendingTail = pendingHead;
    while( pendingTail->next ) pendingTail = pendingTail->next;
  }
  return SQLITE_OK;
}

/* Persist a deterministic arbitrary subset, discard the remainder, then
** terminate without returning from xSync. A stock rollback protocol remains
** recoverable because its journal has already crossed an earlier xSync. */
static void simulatePowerLoss(void){
  PendingWrite *write = pendingHead;
  while( write ){
    PendingWrite *next = write->next;
    if( (nextRandom() & 1u)!=0 ){
      (void)applyPending(write);
      (void)write->file->real->pMethods->xSync(write->file->real,
                                               SQLITE_SYNC_FULL);
    }
    freePending(write);
    write = next;
  }
  pendingHead = pendingTail = 0;
  _exit(99);
}

static int powerClose(sqlite3_file *base){
  PowerFile *file = (PowerFile *)base;
  int rc = flushFile(file);
  int closeRc = file->real->pMethods->xClose(file->real);
  sqlite3_free(file->name);
  file->base.pMethods = 0;
  return rc==SQLITE_OK ? closeRc : rc;
}

static int powerRead(sqlite3_file *base, void *buffer, int amount,
                     sqlite3_int64 offset){
  PowerFile *file = (PowerFile *)base;
  PendingWrite *write;
  int rc = file->real->pMethods->xRead(file->real, buffer, amount, offset);
  if( rc!=SQLITE_OK && rc!=SQLITE_IOERR_SHORT_READ ) return rc;
  for(write=pendingHead; write; write=write->next){
    sqlite3_int64 begin, end, writeEnd;
    if( write->file!=file || write->amount<=0 ) continue;
    writeEnd = write->offset + write->amount;
    begin = write->offset>offset ? write->offset : offset;
    end = writeEnd<(offset+amount) ? writeEnd : (offset+amount);
    if( begin<end ){
      memcpy((unsigned char *)buffer + (begin-offset),
             write->bytes + (begin-write->offset), (size_t)(end-begin));
      rc = SQLITE_OK;
    }
  }
  return rc;
}

static int powerWrite(sqlite3_file *base, const void *buffer, int amount,
                      sqlite3_int64 offset){
  return appendPending((PowerFile *)base, buffer, amount, offset);
}

static int powerTruncate(sqlite3_file *base, sqlite3_int64 size){
  return appendPending((PowerFile *)base, 0, -1, size);
}

static int powerSync(sqlite3_file *base, int flags){
  PowerFile *file = (PowerFile *)base;
  int rc;
  if( crashFile && file->name && strcmp(crashFile, file->name)==0 ){
    if( crashDelay>0 ) crashDelay--;
    if( crashDelay==0 ) simulatePowerLoss();
  }
  rc = flushFile(file);
  if( rc!=SQLITE_OK ) return rc;
  return file->real->pMethods->xSync(file->real, flags);
}

static int powerFileSize(sqlite3_file *base, sqlite3_int64 *size){
  PowerFile *file = (PowerFile *)base;
  PendingWrite *write;
  int rc = file->real->pMethods->xFileSize(file->real, size);
  if( rc!=SQLITE_OK ) return rc;
  for(write=pendingHead; write; write=write->next){
    if( write->file!=file ) continue;
    if( write->amount<0 ) *size = write->offset;
    else if( *size < write->offset + write->amount )
      *size = write->offset + write->amount;
  }
  return SQLITE_OK;
}

static int powerLock(sqlite3_file *base, int lock){
  PowerFile *file = (PowerFile *)base;
  return file->real->pMethods->xLock(file->real, lock);
}
static int powerUnlock(sqlite3_file *base, int lock){
  PowerFile *file = (PowerFile *)base;
  return file->real->pMethods->xUnlock(file->real, lock);
}
static int powerCheckReserved(sqlite3_file *base, int *result){
  PowerFile *file = (PowerFile *)base;
  return file->real->pMethods->xCheckReservedLock(file->real, result);
}
static int powerFileControl(sqlite3_file *base, int op, void *argument){
  PowerFile *file = (PowerFile *)base;
  return file->real->pMethods->xFileControl(file->real, op, argument);
}
static int powerSectorSize(sqlite3_file *base){
  PowerFile *file = (PowerFile *)base;
  return file->real->pMethods->xSectorSize(file->real);
}
static int powerCharacteristics(sqlite3_file *base){
  PowerFile *file = (PowerFile *)base;
  /* Do not promise atomic or sequential persistence to the pager. */
  return file->real->pMethods->xDeviceCharacteristics(file->real) &
    ~(SQLITE_IOCAP_ATOMIC | SQLITE_IOCAP_ATOMIC512 | SQLITE_IOCAP_ATOMIC1K |
      SQLITE_IOCAP_ATOMIC2K | SQLITE_IOCAP_ATOMIC4K | SQLITE_IOCAP_ATOMIC8K |
      SQLITE_IOCAP_ATOMIC16K | SQLITE_IOCAP_ATOMIC32K |
      SQLITE_IOCAP_ATOMIC64K | SQLITE_IOCAP_SAFE_APPEND |
      SQLITE_IOCAP_SEQUENTIAL);
}

static const sqlite3_io_methods powerIo = {
  1, powerClose, powerRead, powerWrite, powerTruncate, powerSync,
  powerFileSize, powerLock, powerUnlock, powerCheckReserved,
  powerFileControl, powerSectorSize, powerCharacteristics,
  0, 0, 0, 0,                 /* Version-2 shared-memory/WAL methods. */
  0, 0                        /* Version-3 memory-mapped I/O methods. */
};

static int powerOpen(sqlite3_vfs *vfs, const char *name, sqlite3_file *base,
                     int flags, int *outFlags){
  PowerFile *file = (PowerFile *)base;
  sqlite3_vfs *realVfs = underlying(vfs);
  int rc;
  memset(file, 0, sizeof(*file));
  file->real = (sqlite3_file *)&file[1];
  rc = realVfs->xOpen(realVfs, name, file->real, flags, outFlags);
  if( rc!=SQLITE_OK ) return rc;
  file->name = sqlite3_mprintf("%s", name ? name : "");
  if( file->name==0 ){
    file->real->pMethods->xClose(file->real);
    return SQLITE_NOMEM;
  }
  file->base.pMethods = &powerIo;
  return SQLITE_OK;
}

static int powerDelete(sqlite3_vfs *vfs, const char *name, int syncDir){
  sqlite3_vfs *realVfs = underlying(vfs);
  return realVfs->xDelete(realVfs, name, syncDir);
}
static int powerAccess(sqlite3_vfs *vfs, const char *name, int flags, int *out){
  sqlite3_vfs *realVfs = underlying(vfs);
  return realVfs->xAccess(realVfs, name, flags, out);
}
static int powerFullPath(sqlite3_vfs *vfs, const char *name, int n, char *out){
  sqlite3_vfs *realVfs = underlying(vfs);
  return realVfs->xFullPathname(realVfs, name, n, out);
}
static void *powerDlOpen(sqlite3_vfs *vfs, const char *name){
  sqlite3_vfs *realVfs = underlying(vfs);
  return realVfs->xDlOpen(realVfs, name);
}
static void powerDlError(sqlite3_vfs *vfs, int n, char *out){
  sqlite3_vfs *realVfs = underlying(vfs);
  realVfs->xDlError(realVfs, n, out);
}
static void (*powerDlSym(sqlite3_vfs *vfs, void *handle,
                         const char *symbol))(void){
  sqlite3_vfs *realVfs = underlying(vfs);
  return realVfs->xDlSym(realVfs, handle, symbol);
}
static void powerDlClose(sqlite3_vfs *vfs, void *handle){
  sqlite3_vfs *realVfs = underlying(vfs);
  realVfs->xDlClose(realVfs, handle);
}
static int powerRandomness(sqlite3_vfs *vfs, int n, char *out){
  sqlite3_vfs *realVfs = underlying(vfs);
  return realVfs->xRandomness(realVfs, n, out);
}
static int powerSleep(sqlite3_vfs *vfs, int microseconds){
  sqlite3_vfs *realVfs = underlying(vfs);
  return realVfs->xSleep(realVfs, microseconds);
}
static int powerCurrentTime(sqlite3_vfs *vfs, double *time){
  sqlite3_vfs *realVfs = underlying(vfs);
  return realVfs->xCurrentTime(realVfs, time);
}
static int powerLastError(sqlite3_vfs *vfs, int n, char *out){
  sqlite3_vfs *realVfs = underlying(vfs);
  return realVfs->xGetLastError ? realVfs->xGetLastError(realVfs, n, out) : 0;
}

static int registerPowerVfs(void){
  sqlite3_vfs *realVfs = sqlite3_vfs_find(0);
  if( sqlite3_vfs_find("powerloss") ) return SQLITE_OK;
  if( realVfs==0 ) return SQLITE_ERROR;
  memset(&powerVfs, 0, sizeof(powerVfs));
  powerVfs.iVersion = 1;
  powerVfs.szOsFile = (int)sizeof(PowerFile) + realVfs->szOsFile;
  powerVfs.mxPathname = realVfs->mxPathname;
  powerVfs.zName = "powerloss";
  powerVfs.pAppData = realVfs;
  powerVfs.xOpen = powerOpen;
  powerVfs.xDelete = powerDelete;
  powerVfs.xAccess = powerAccess;
  powerVfs.xFullPathname = powerFullPath;
  powerVfs.xDlOpen = powerDlOpen;
  powerVfs.xDlError = powerDlError;
  powerVfs.xDlSym = powerDlSym;
  powerVfs.xDlClose = powerDlClose;
  powerVfs.xRandomness = powerRandomness;
  powerVfs.xSleep = powerSleep;
  powerVfs.xCurrentTime = powerCurrentTime;
  powerVfs.xGetLastError = powerLastError;
  return sqlite3_vfs_register(&powerVfs, 0);
}

static void configurePowerLoss(sqlite3_context *context, int argc,
                               sqlite3_value **argv){
  const unsigned char *name;
  (void)argc;
  crashDelay = sqlite3_value_int(argv[0]);
  name = sqlite3_value_text(argv[1]);
  sqlite3_free(crashFile);
  crashFile = sqlite3_mprintf("%s", name ? (const char *)name : "");
  crashRandom = (uint32_t)sqlite3_value_int64(argv[2]);
  if( crashRandom==0 ) crashRandom = 1;
  sqlite3_result_int(context, crashFile!=0 ? 1 : 0);
}

#ifdef _WIN32
__declspec(dllexport)
#endif
int sqlite3_powerlossvfs_init(sqlite3 *db, char **error,
                              const sqlite3_api_routines *api){
  int rc;
  SQLITE_EXTENSION_INIT2(api);
  rc = registerPowerVfs();
  if( rc!=SQLITE_OK ){
    if( error ) *error = sqlite3_mprintf("powerloss VFS registration failed");
    return rc;
  }
  return sqlite3_create_function(db, "powerloss_config", 3,
    SQLITE_UTF8 | SQLITE_DIRECTONLY, 0, configurePowerLoss, 0, 0);
}
