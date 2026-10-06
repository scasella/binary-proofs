#!/bin/bash
set -euo pipefail
cd /work
test ! -e /output/c2.so
sha256sum -c clients/header-sha256.txt > /output/header-binding.txt
cmp artifacts/baseline/libc.so.6 /lib/x86_64-linux-gnu/libc.so.6
cmp artifacts/baseline/libcrypto.so.3 /usr/lib/x86_64-linux-gnu/libcrypto.so.3
cc --version > /output/compiler.txt
cc -I/work/artifacts/client-headers/extracted/usr/include \
   -I/work/artifacts/client-headers/extracted/usr/include/x86_64-linux-gnu \
   -O2 -fPIC -fno-builtin -fno-builtin-memcmp -fno-inline -fno-ipa-cp \
   -fno-lto -fno-optimize-sibling-calls -Wall -Wextra -shared \
   /c2-inputs/c2.c -L/work/artifacts/baseline \
   -Wl,-z,now -Wl,-z,relro -Wl,-rpath,/work/artifacts/baseline \
   -Wl,--no-as-needed -l:libcrypto.so.3 -l:libc.so.6 -o /output/c2.so
sha256sum /c2-inputs/c2.c /output/c2.so > /output/build-sha256.txt
