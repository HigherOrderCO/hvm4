#!/bin/bash
set -e

cd "$(dirname "$0")/clang"

echo "Building hvm4..."
clang -O2 -o hvm4 main.c

echo "Installing to /usr/local/bin/hvm4..."
sudo mv hvm4 /usr/local/bin/hvm4

echo "Done! You can now run: hvm4 file.hvm4"
