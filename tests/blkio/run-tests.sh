#!/bin/bash

set -e

export RUST_LOG="${RUST_LOG:-debug}"

exit_code=0
PROJECT_ROOT=$(pwd)
# To find the vhost-backend and init-metadata binaries
export PATH=$(pwd)/target/debug:$PATH
cd target/tests/blkio

LOG_FILE="vhost-backend.log"
: > "$LOG_FILE"

echo "Setting up disk..."
# Always create/recreate these files
rm -f disk.raw disk.metadata base.raw
echo "Creating disk files (always recreated)..."
truncate --size 4M disk.raw
truncate --size 8K disk.metadata

echo "Creating base image with pattern..."
make -C $PROJECT_ROOT populate-base-image

# Generate AES-XTS keys for disk encryption
echo "Generating AES-XTS keys for disk encryption..."
raw_key=$(openssl rand 64)
key1=$(echo -n "$raw_key" | head -c 32 | base64 -w 0)
key2=$(echo -n "$raw_key" | tail -c 32 | base64 -w 0)

CONFIG_FILE="ubiblk-config.yaml"
echo "Creating $CONFIG_FILE..."
cat > "$CONFIG_FILE" << EOF
path: "disk.raw"
image_path: "base.raw"
metadata_path: "disk.metadata"
socket: "vhost.sock"
num_queues: 4
queue_size: 256
seg_size_max: 4096
seg_count_max: 1
poll_queue_timeout_us: 500
device_id: "vm123456"
encryption_key:
- $key1
- $key2
EOF

STRIPE_SECTOR_COUNT_SHIFT=${STRIPE_SECTOR_COUNT_SHIFT:-11}
if ! [[ "$STRIPE_SECTOR_COUNT_SHIFT" =~ ^[0-9]+$ ]] || [ "$STRIPE_SECTOR_COUNT_SHIFT" -lt 1 ] || \
    [ "$STRIPE_SECTOR_COUNT_SHIFT" -gt 18 ]; then
    echo "Error: STRIPE_SECTOR_COUNT_SHIFT must be a positive integer between 1 and 18"
    exit 1
fi
echo "Initializing metadata with stripe sector count shift: $STRIPE_SECTOR_COUNT_SHIFT"
init-metadata --config "$CONFIG_FILE" --stripe-sector-count-shift "$STRIPE_SECTOR_COUNT_SHIFT"

echo "Starting vhost-backend in background..."
vhost-backend --config "$CONFIG_FILE" >"$LOG_FILE" 2>&1 &
VHOST_PID=$!
echo "vhost-backend started with PID: $VHOST_PID"

echo $VHOST_PID > vhost-backend.pid
echo "PID stored in vhost-backend.pid"

sleep 1

echo "Running lazy-read test..."
make -C $PROJECT_ROOT test-lazy-read

echo "Running write-read test..."
make -C $PROJECT_ROOT test-write-read

echo "Running encryption test..."
make -C $PROJECT_ROOT test-write-encrypted-data
echo "Checking encryption by reading raw disk data..."
# Read 4KB from 3MB offset in the raw disk file
dd if=disk.raw of=test_read.bin bs=4096 count=1 skip=768 2>/dev/null
# Check if the data contains 'A's (it shouldn't if encryption is working)
# 'A' in hex is 41, so we're looking for a sequence of 41s
if hexdump -C test_read.bin | grep -q "41 41 41 41"; then
    echo "ERROR: Encryption test failed - raw disk data contains 'A's"
    exit_code=1
else
    echo "SUCCESS: Encryption test passed - raw disk data does not contain 'A's"
fi

echo "Stopping vhost-backend (PID: $VHOST_PID)..."
kill $VHOST_PID
wait $VHOST_PID 2>/dev/null || true
rm -f vhost-backend.pid
echo "Tests complete."
exit $exit_code
