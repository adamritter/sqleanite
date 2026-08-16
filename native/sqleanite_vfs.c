#include <lean/lean.h>

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

LEAN_EXPORT lean_obj_res sqleanite_process_alive(size_t process,
                                                   lean_obj_arg world) {
  (void)world;
  int alive = kill((pid_t)process, 0) == 0 || errno == EPERM;
  return lean_io_result_mk_ok(lean_box(alive));
}

static lean_obj_res sqleanite_io_error(const char *operation,
                                         const char *path,
                                         int error_number) {
  char message[1024];
  snprintf(message, sizeof(message), "%s(%s): %s", operation, path,
           strerror(error_number));
  return lean_io_result_mk_error(
      lean_mk_io_user_error(lean_mk_string(message)));
}

LEAN_EXPORT lean_obj_res sqleanite_fdatasync_path(b_lean_obj_arg path_object,
                                                    lean_obj_arg world) {
  (void)world;
  const char *path = lean_string_cstr(path_object);
  int descriptor = open(path, O_RDONLY | O_CLOEXEC);
  if (descriptor < 0) {
    return sqleanite_io_error("open", path, errno);
  }
  if (fdatasync(descriptor) != 0) {
    int error_number = errno;
    close(descriptor);
    return sqleanite_io_error("fdatasync", path, error_number);
  }
  if (close(descriptor) != 0) {
    return sqleanite_io_error("close", path, errno);
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res
sqleanite_fsync_parent_path(b_lean_obj_arg path_object, lean_obj_arg world) {
  (void)world;
  const char *path = lean_string_cstr(path_object);
  char directory[4096];
  size_t length = strlen(path);
  if (length >= sizeof(directory)) {
    return sqleanite_io_error("parent", path, ENAMETOOLONG);
  }
  memcpy(directory, path, length + 1);
  char *slash = strrchr(directory, '/');
  if (slash == NULL) {
    memcpy(directory, ".", 2);
  } else if (slash == directory) {
    directory[1] = '\0';
  } else {
    *slash = '\0';
  }
  int descriptor = open(directory, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
  if (descriptor < 0) {
    return sqleanite_io_error("open-directory", directory, errno);
  }
  if (fsync(descriptor) != 0) {
    int error_number = errno;
    close(descriptor);
    return sqleanite_io_error("fsync-directory", directory, error_number);
  }
  if (close(descriptor) != 0) {
    return sqleanite_io_error("close-directory", directory, errno);
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res sqleanite_pread_bytes(b_lean_obj_arg path_object,
                                                uint64_t offset,
                                                size_t length,
                                                lean_obj_arg world) {
  (void)world;
  const char *path = lean_string_cstr(path_object);
  int descriptor = open(path, O_RDONLY | O_CLOEXEC);
  if (descriptor < 0) {
    return sqleanite_io_error("open", path, errno);
  }
  lean_object *bytes = lean_alloc_sarray(1, length, length);
  size_t completed = 0;
  while (completed < length) {
    ssize_t amount = pread(descriptor, lean_sarray_cptr(bytes) + completed,
                           length - completed, (off_t)(offset + completed));
    if (amount < 0) {
      if (errno == EINTR) continue;
      int error_number = errno;
      close(descriptor);
      lean_dec(bytes);
      return sqleanite_io_error("pread", path, error_number);
    }
    if (amount == 0) break;
    completed += (size_t)amount;
  }
  if (close(descriptor) != 0) {
    int error_number = errno;
    lean_dec(bytes);
    return sqleanite_io_error("close", path, error_number);
  }
  if (completed != length) lean_sarray_set_size(bytes, completed);
  return lean_io_result_mk_ok(bytes);
}

LEAN_EXPORT lean_obj_res sqleanite_pwrite_bytes(b_lean_obj_arg path_object,
                                                 uint64_t offset,
                                                 b_lean_obj_arg bytes,
                                                 lean_obj_arg world) {
  (void)world;
  const char *path = lean_string_cstr(path_object);
  int descriptor = open(path, O_WRONLY | O_CLOEXEC);
  if (descriptor < 0) {
    return sqleanite_io_error("open", path, errno);
  }
  size_t length = lean_sarray_size(bytes);
  size_t completed = 0;
  while (completed < length) {
    ssize_t amount = pwrite(descriptor, lean_sarray_cptr(bytes) + completed,
                            length - completed, (off_t)(offset + completed));
    if (amount < 0) {
      if (errno == EINTR) continue;
      int error_number = errno;
      close(descriptor);
      return sqleanite_io_error("pwrite", path, error_number);
    }
    completed += (size_t)amount;
  }
  if (close(descriptor) != 0) {
    return sqleanite_io_error("close", path, errno);
  }
  return lean_io_result_mk_ok(lean_box(0));
}

/* PageTransfer stores one object field (ByteArray) followed by one UInt64. */
static b_lean_obj_arg sqleanite_transfer_bytes(b_lean_obj_arg transfer) {
  return lean_ctor_get(transfer, 0);
}

static uint64_t sqleanite_transfer_offset(b_lean_obj_arg transfer) {
  return lean_ctor_get_uint64(transfer, sizeof(void *));
}

/* Iterate a Lean-selected page list without building one native IO continuation
 * per page.  This is deliberately only a VFS loop: offsets, order, and bytes
 * are all supplied by Lean's verified transaction planner. */
LEAN_EXPORT lean_obj_res sqleanite_pwrite_pages(b_lean_obj_arg path_object,
                                                 b_lean_obj_arg transfers,
                                                 lean_obj_arg world) {
  (void)world;
  const char *path = lean_string_cstr(path_object);
  int descriptor = open(path, O_WRONLY | O_CLOEXEC);
  if (descriptor < 0) {
    return sqleanite_io_error("open", path, errno);
  }
  size_t transfer_count = lean_array_size(transfers);
  for (size_t i = 0; i < transfer_count; ++i) {
    b_lean_obj_arg transfer = lean_array_get_core(transfers, i);
    b_lean_obj_arg bytes = sqleanite_transfer_bytes(transfer);
    uint64_t offset = sqleanite_transfer_offset(transfer);
    size_t length = lean_sarray_size(bytes);
    size_t completed = 0;
    while (completed < length) {
      ssize_t amount = pwrite(descriptor, lean_sarray_cptr(bytes) + completed,
                              length - completed,
                              (off_t)(offset + completed));
      if (amount < 0) {
        if (errno == EINTR) continue;
        int error_number = errno;
        close(descriptor);
        return sqleanite_io_error("pwrite-pages", path, error_number);
      }
      completed += (size_t)amount;
    }
  }
  if (close(descriptor) != 0) {
    return sqleanite_io_error("close", path, errno);
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res sqleanite_verify_pages(b_lean_obj_arg path_object,
                                                 b_lean_obj_arg transfers,
                                                 lean_obj_arg world) {
  (void)world;
  const char *path = lean_string_cstr(path_object);
  int descriptor = open(path, O_RDONLY | O_CLOEXEC);
  if (descriptor < 0) {
    return sqleanite_io_error("open", path, errno);
  }
  uint8_t *actual = NULL;
  size_t capacity = 0;
  size_t transfer_count = lean_array_size(transfers);
  for (size_t i = 0; i < transfer_count; ++i) {
    b_lean_obj_arg transfer = lean_array_get_core(transfers, i);
    b_lean_obj_arg expected = sqleanite_transfer_bytes(transfer);
    uint64_t offset = sqleanite_transfer_offset(transfer);
    size_t length = lean_sarray_size(expected);
    if (capacity < length) {
      uint8_t *resized = realloc(actual, length);
      if (resized == NULL) {
        free(actual);
        close(descriptor);
        return sqleanite_io_error("verify-pages-allocate", path, ENOMEM);
      }
      actual = resized;
      capacity = length;
    }
    size_t completed = 0;
    while (completed < length) {
      ssize_t amount = pread(descriptor, actual + completed,
                             length - completed,
                             (off_t)(offset + completed));
      if (amount < 0) {
        if (errno == EINTR) continue;
        int error_number = errno;
        free(actual);
        close(descriptor);
        return sqleanite_io_error("pread-pages", path, error_number);
      }
      if (amount == 0) {
        free(actual);
        close(descriptor);
        return sqleanite_io_error("pread-pages-short", path, EIO);
      }
      completed += (size_t)amount;
    }
    if (memcmp(actual, lean_sarray_cptr(expected), length) != 0) {
      free(actual);
      close(descriptor);
      return sqleanite_io_error("verify-pages-mismatch", path, EIO);
    }
  }
  free(actual);
  if (close(descriptor) != 0) {
    return sqleanite_io_error("close", path, errno);
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res sqleanite_rename_path(b_lean_obj_arg source_object,
                                                b_lean_obj_arg target_object,
                                                lean_obj_arg world) {
  (void)world;
  const char *source = lean_string_cstr(source_object);
  const char *target = lean_string_cstr(target_object);
  if (renameat(AT_FDCWD, source, AT_FDCWD, target) != 0) {
    return sqleanite_io_error("renameat", source, errno);
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res sqleanite_unlink_path(b_lean_obj_arg path_object,
                                                lean_obj_arg world) {
  (void)world;
  const char *path = lean_string_cstr(path_object);
  if (unlinkat(AT_FDCWD, path, 0) != 0) {
    return sqleanite_io_error("unlinkat", path, errno);
  }
  return lean_io_result_mk_ok(lean_box(0));
}
