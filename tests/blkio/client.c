#include <blkio.h>
#include <errno.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static bool debug_enabled = false;
const char *driver = "virtio-blk-vhost-user";
const char *socket_path = "target/tests/blkio/vhost.sock";

typedef void (*blkioq_fn)(struct blkioq *, uint64_t, void *, size_t, void *,
                          uint32_t);

struct context {
  struct blkio *bio;
  struct blkioq *q;
  struct blkio_mem_region write_region;
  struct blkio_mem_region read_region;
};

void cleanup(struct context *ctx) {
  if (ctx->bio)
    blkio_destroy(&ctx->bio);
}

int handle_error(struct context *ctx, const char *msg, int ret) {
  printf("%s: %d (%s), error_msg=%s\n", msg, ret, strerror(-ret),
         blkio_get_error_msg());
  cleanup(ctx);
  return 1;
}

int init_context(struct context *ctx, const char *driver, const char *path) {
  if (access(path, F_OK) != 0)
    return handle_error(ctx, "Ubiblk socket file does not exist", -ENOENT);

  int ret = blkio_create(driver, &ctx->bio);
  if (ret < 0)
    return handle_error(ctx, "Failed to create blkio driver", ret);

  ret = blkio_set_str(ctx->bio, "path", path);
  if (ret < 0)
    return handle_error(ctx, "Error setting path", ret);

  ret = blkio_connect(ctx->bio);
  if (ret < 0)
    return handle_error(ctx, "Error connecting", ret);

  ret = blkio_start(ctx->bio);
  if (ret < 0)
    return handle_error(ctx, "Error starting", ret);

  ctx->q = blkio_get_queue(ctx->bio, 0);
  if (!ctx->q)
    return handle_error(ctx, "Error getting queue", -ENOMEM);

  return 0;
}

int setup_mem_region(struct context *ctx, struct blkio_mem_region *region,
                     size_t size, const char *name) {
  int ret = blkio_alloc_mem_region(ctx->bio, region, size);
  if (ret < 0)
    return handle_error(ctx, "Error allocating memory region", ret);
  printf("Allocated %s memory region: addr=%p, len=%zu, fd=%d, fd_offset=%ld\n",
         name, region->addr, region->len, region->fd, region->fd_offset);

  ret = blkio_map_mem_region(ctx->bio, region);
  if (ret < 0)
    return handle_error(ctx, "Error mapping memory region", ret);
  printf("Successfully mapped %s memory region of %zu bytes\n", name, size);
  return 0;
}

int do_io(struct context *ctx, blkioq_fn io_func, uint64_t offset, void *buf,
          size_t size, const char *op) {
  struct blkio_completion completion = {0};
  io_func(ctx->q, offset, buf, size, NULL, 0);
  int ret = blkioq_do_io(ctx->q, &completion, 1, 1, NULL);
  if (ret != 1)
    return handle_error(ctx, "Error in blkioq_do_io", ret);
  if (completion.ret != 0) {
    printf("%s failed: ret=%d (%s), error_msg=%s\n", op, completion.ret,
           strerror(-completion.ret),
           completion.error_msg ? completion.error_msg : "none");
    cleanup(ctx);
    return 1;
  }
  if (debug_enabled)
    printf("Successfully %s %zu bytes to/from offset 0x%lx\n", op, size,
           offset);
  return 0;
}

int write_read_test_with_block_size(size_t block_size) {
  struct context ctx = {0};
  size_t total_size = 4 * 1024 * 1024;
  uint64_t offset = 0;

  printf("Running write-read test with block size: %zu bytes\n", block_size);

  if (init_context(&ctx, driver, socket_path))
    return 1;

  if (setup_mem_region(&ctx, &ctx.write_region, block_size, "write"))
    return 1;

  if (setup_mem_region(&ctx, &ctx.read_region, block_size, "read"))
    return 1;

  unsigned char *random_data = malloc(block_size);
  if (!random_data) {
    printf("Error allocating memory for random data\n");
    cleanup(&ctx);
    return 1;
  }
  FILE *urandom = fopen("/dev/urandom", "r");
  if (!urandom) {
    printf("Error opening /dev/urandom\n");
    free(random_data);
    cleanup(&ctx);
    return 1;
  }
  fread(random_data, 1, block_size, urandom);
  fclose(urandom);

  while (offset < total_size) {
    memcpy(ctx.write_region.addr, random_data, block_size);

    if (do_io(&ctx, (blkioq_fn)blkioq_write, offset, ctx.write_region.addr,
              block_size, "write"))
      return 1;

    if (do_io(&ctx, blkioq_read, offset, ctx.read_region.addr, block_size,
              "read"))
      return 1;

    if (memcmp(ctx.read_region.addr, random_data, block_size) == 0) {
      if (debug_enabled)
        printf("Validation successful: read data matches written data at "
               "offset 0x%lx\n",
               offset);
    } else {
      printf("Validation failed: read data does not match written data at "
             "offset 0x%lx\n",
             offset);
      printf("First 16 bytes read: ");
      for (size_t i = 0; i < 16; i++)
        printf("%02x ", ((unsigned char *)ctx.read_region.addr)[i]);
      printf("\nExpected: ");
      for (size_t i = 0; i < 16; i++)
        printf("%02x ", random_data[i]);
      printf("\n");
      free(random_data);
      cleanup(&ctx);
      return 1;
    }
    offset += block_size;
  }

  if (!debug_enabled)
    printf("All write blocks tested successfully with block size: %zu bytes\n",
           block_size);

  free(random_data);
  cleanup(&ctx);
  return 0;
}

int write_read_test() {
  // Test with different block sizes: 4KB, 16KB, and 64KB
  size_t block_sizes[] = {4096, 16384, 65536};
  size_t num_block_sizes = sizeof(block_sizes) / sizeof(block_sizes[0]);

  for (size_t i = 0; i < num_block_sizes; i++) {
    if (write_read_test_with_block_size(block_sizes[i]) != 0) {
      return 1;
    }
    // everytime we do a blkio_destroy, the vhost-backend restarts
    // so we would wait for a second for it to become running again
    sleep(1);
  }

  printf("All write-read tests completed successfully with all block sizes\n");
  return 0;
}

int lazy_read_test() {
  struct context ctx = {0};
  size_t block_size = 4 * 1024;
  size_t total_size = 2 * 1024 * 1024;
  uint64_t offset = 0;

  printf("Running lazy read test\n");

  if (init_context(&ctx, driver, socket_path))
    return 1;

  if (setup_mem_region(&ctx, &ctx.read_region, block_size, "read"))
    return 1;

  while (offset < total_size) {
    if (do_io(&ctx, blkioq_read, offset, ctx.read_region.addr, block_size,
              "read"))
      return 1;

    // Validate the data read matches the expected pattern: (byte_offset * 111)
    // & 0xff
    unsigned char *data = (unsigned char *)ctx.read_region.addr;
    int valid = 1;
    for (size_t i = 0; i < block_size; i++) {
      unsigned char expected = ((offset + i) * 111) & 0xff;
      if (data[i] != expected) {
        valid = 0;
        printf(
            "Validation failed at offset 0x%lx: expected 0x%02x, got 0x%02x\n",
            offset + i, expected, data[i]);
        break;
      }
    }

    if (!valid) {
      cleanup(&ctx);
      return 1;
    }

    if (debug_enabled && (offset % (1024 * 1024) == 0))
      printf("Validated %lu MB of lazy reads\n", offset / (1024 * 1024));

    offset += block_size;
  }

  printf("Lazy read test completed successfully\n");

  cleanup(&ctx);
  return 0;
}

int encryption_test() {
  struct context ctx = {0};
  size_t block_size = 4 * 1024;
  uint64_t offset = 3 * 1024 * 1024;

  printf("Running encryption test\n");

  if (init_context(&ctx, driver, socket_path))
    return 1;

  if (setup_mem_region(&ctx, &ctx.write_region, block_size, "write"))
    return 1;

  // Fill buffer with 'A' characters
  memset(ctx.write_region.addr, 'A', block_size);

  // Write the 'A's to the 3MB offset
  if (do_io(&ctx, (blkioq_fn)blkioq_write, offset, ctx.write_region.addr,
            block_size, "write"))
    return 1;

  printf("Successfully wrote 'A' characters to offset 3MB (0x%lx)\n", offset);

  cleanup(&ctx);
  return 0;
}

int main(int argc, char *argv[]) {
  const char *test_mode = getenv("TEST_MODE");
  const char *debug_env = getenv("DEBUG");

  if (debug_env &&
      (strcmp(debug_env, "true") == 0 || strcmp(debug_env, "1") == 0)) {
    debug_enabled = true;
  }

  if (test_mode == NULL) {
    test_mode = "write_read";
  }

  if (strcmp(test_mode, "write_read") == 0) {
    return write_read_test();
  } else if (strcmp(test_mode, "lazy_read") == 0) {
    return lazy_read_test();
  } else if (strcmp(test_mode, "write_encrypted_data") == 0) {
    return encryption_test();
  } else {
    printf("Invalid TEST_MODE value: %s\n", test_mode);
    printf("Valid options are: 'write_read' (default), 'lazy_read', or "
           "'write_encrypted_data'\n");
    return 1;
  }
}
