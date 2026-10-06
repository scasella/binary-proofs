#include <stddef.h>
#include <openssl/crypto.h>

int c1_crypto_buffers_equal(const void *a, const void *b, size_t n) {
    return CRYPTO_memcmp(a, b, n) == 0;
}
