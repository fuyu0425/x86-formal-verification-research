#!/usr/bin/env bash
# Links libc.a's memrchr variants (needs `bash get-libc.sh` first) into native.c and runs it.
# Needs a CPU with AVX2, BMI2, LZCNT and AVX-512F/VL/BW.
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT
cd "$work"
ar x "$here/../glibc-2.43-ubuntu-26.04-amd64/libc.a" memrchr-sse2.o memrchr-avx2.o memrchr-evex.o
gcc -O2 -o native "$here/native.c" memrchr-sse2.o memrchr-avx2.o memrchr-evex.o
./native "$@"
