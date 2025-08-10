#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[]) {
  if (argc != 3) {
    fprintf(stderr, "Usage: %s <filename> <size_in_bytes>\n", argv[0]);
    return 1;
  }

  const char *filename = argv[1];
  size_t size = strtoull(argv[2], NULL, 10);

  FILE *file = fopen(filename, "wb");
  if (!file) {
    perror("Error opening file");
    return 1;
  }

  const size_t buffer_size = 64 * 1024;
  uint8_t *buffer = malloc(buffer_size);
  if (!buffer) {
    fprintf(stderr, "Error allocating buffer\n");
    fclose(file);
    return 1;
  }

  size_t written = 0;
  while (written < size) {
    size_t to_write =
        (size - written < buffer_size) ? (size - written) : buffer_size;

    // Fill buffer with the pattern: (byte_offset * 111) & 0xff
    for (size_t i = 0; i < to_write; i++) {
      buffer[i] = ((written + i) * 111) & 0xff;
    }

    size_t result = fwrite(buffer, 1, to_write, file);
    if (result != to_write) {
      perror("Error writing to file");
      free(buffer);
      fclose(file);
      return 1;
    }

    written += to_write;
  }

  free(buffer);
  fclose(file);

  printf("Successfully created %s with size %zu bytes\n", filename, size);
  return 0;
}
