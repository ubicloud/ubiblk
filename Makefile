CC = gcc
CFLAGS = -I/usr/local/include
LDFLAGS = -L/usr/local/lib/x86_64-linux-gnu -Wl,-rpath,/usr/local/lib/x86_64-linux-gnu -lblkio

TESTS_DIR = tests/blkio
TARGET_TESTS_DIR = target/tests/blkio

all: test-client create-base-image

test-client: $(TESTS_DIR)/client.c
	$(CC) -o $(TARGET_TESTS_DIR)/client $(TESTS_DIR)/client.c $(CFLAGS) $(LDFLAGS)

create-base-image: $(TESTS_DIR)/create_base_image.c
	$(CC) -o $(TARGET_TESTS_DIR)/create_base_image $(TESTS_DIR)/create_base_image.c $(CFLAGS)

build-ubiblk:
	cargo build

populate-base-image: create-base-image
	./$(TARGET_TESTS_DIR)/create_base_image $(TARGET_TESTS_DIR)/base.raw 2097152

test-write-read: test-client
	TEST_MODE=write_read ./$(TARGET_TESTS_DIR)/client

test-lazy-read: test-client
	TEST_MODE=lazy_read ./$(TARGET_TESTS_DIR)/client

test-write-encrypted-data: test-client
	TEST_MODE=write_encrypted_data ./$(TARGET_TESTS_DIR)/client

test-e2e: test-client build-ubiblk
	./$(TESTS_DIR)/run-tests.sh

test-e2e-verbose: test-client build-ubiblk
	RUST_LOG=debug RUST_BACKTRACE=full DEBUG=1 ./$(TESTS_DIR)/run-tests.sh

format-tests:
	clang-format -i $(TESTS_DIR)/*.c

.PHONY: all test-client test-verbose test-write-read format-tests build-ubiblk
