#!/bin/bash
set -euo pipefail
cd /work
test ! -e /output/c3.so
cmp artifacts/baseline/libc.so.6 /lib/x86_64-linux-gnu/libc.so.6
cmp artifacts/baseline/libcrypto.so.3 /usr/lib/x86_64-linux-gnu/libcrypto.so.3
sha256sum artifacts/baseline/libc.so.6 artifacts/baseline/libcrypto.so.3 > /output/supplier-binding.txt
cc --version > /output/compiler.txt
as --version > /output/assembler.txt
cc -fPIC -fno-lto -shared /c3-inputs/c3.S -L/work/artifacts/baseline \
  -Wl,-z,now -Wl,-z,relro -Wl,-rpath,/work/artifacts/baseline \
  -Wl,--no-as-needed -l:libcrypto.so.3 -l:libc.so.6 -o /output/c3.so
sha256sum /c3-inputs/c3.S /output/c3.so > /output/build-sha256.txt
objdump -d -w -Mintel /output/c3.so > /output/disassembly.txt
readelf -aW /output/c3.so > /output/readelf.txt
mkdir /output/gnu-v1
objcopy --dump-section .text=/output/gnu-v1/gnu-text.bin /output/c3.so
objcopy --dump-section .plt=/output/gnu-v1/gnu-plt.bin /output/c3.so
nm -D -S /output/c3.so > /output/gnu-v1/nm-dynamic.txt
