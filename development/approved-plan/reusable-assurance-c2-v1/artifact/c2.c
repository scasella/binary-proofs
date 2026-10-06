#include <stddef.h>
#include <openssl/crypto.h>

/* Authored experimental client; no caller trace claim. */
int c2_equal_and_clear_if_equal(void *secret, const void *expected, size_t n) {
    int equal = (CRYPTO_memcmp(secret, expected, n) == 0);
    if (equal) OPENSSL_cleanse(secret, n);
    return equal;
}
