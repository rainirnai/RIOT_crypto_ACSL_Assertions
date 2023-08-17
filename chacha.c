/*
 * Copyright (C) 2008  D. J. Bernstein  (dedicated to the public domain)
 * Copyright (C) 2015  René Kijewski  <rene.kijewski@fu-berlin.de>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

/*
 * Please notice:
 *  - This implementation of the ChaCha stream cipher is very stripped down.
 *  - It assumes a little-endian system.
 *  - It is implemented for little code and data size, but will likely be
 *    slower than the refenrence implementation. Optimized implementation will
 *    out-perform the code even more.
 */

#include "chacha.h"
#include "byteorder.h"

#if __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#   error \
    "This code is implementented in a way that it will only work for little-endian systems!"
#endif

#include <string.h>

/*@ requires \valid(d);
    requires \valid_read(a); 
    requires \valid_read(b);
    requires c == 16 || c == 12 || c == 8 || c == 7;
    assigns *d,*a;
*/

static void _r(uint32_t *d, uint32_t *a, const uint32_t *b, unsigned c)
{
    *a += *b;
    uint32_t tmp = *a ^ *d;
    *d = (tmp << c) | (tmp >> (32 - c));
}

/*@ requires \valid(input+(0..15));
    requires rounds == 20 || rounds == 12 || rounds == 8;
    requires (rounds * 4) > INT_MIN && (rounds * 4) < INT_MAX;
*/

static void _doubleround(void *output_, const uint32_t input[16],
                         uint8_t rounds)
{
    uint32_t *output = (uint32_t *)output_;
    //Since input and output are uint32_t type and memcpy's third parameter is no of bytes 
    //@ assert \valid(output+(0..15));
    //@ assert \valid(input+(0..15));
    memcpy(output, input, 64);

    rounds *= 4;
    for (unsigned i = 0; i < rounds; ++i) {
        /* cppcheck-suppress duplicateExpressionTernary
         * (reason: Externally imported code beautification) */
        uint32_t *a = &output[((i + ((i & 4) ? 0 : 0)) & 3) + (4 * 0)];
        uint32_t *b = &output[((i + ((i & 4) ? 1 : 0)) & 3) + (4 * 1)];
        uint32_t *c = &output[((i + ((i & 4) ? 2 : 0)) & 3) + (4 * 2)];
        uint32_t *d = &output[((i + ((i & 4) ? 3 : 0)) & 3) + (4 * 3)];

        _r(d, a, b, 16);
        _r(b, c, d, 12);
        _r(d, a, b,  8);
        _r(b, c, d,  7);
    }

    for (unsigned i = 0; i < 16; ++i) {
        output[i] += input[i];
    }
}

/*@
    predicate valid_chacha_ctx(chacha_ctx* ctx) = 
        \valid(ctx) && 
        \valid(ctx->state + (0..15)) &&
        (ctx->rounds == 20 || ctx->rounds == 12 || ctx->rounds == 8);
*/

/*@
  requires \valid(ctx);
  requires \valid(ctx->state + (0..15));
  requires (ctx->rounds == 20 || ctx->rounds == 12 || ctx->rounds == 8);
  requires \valid(key+(0..keylen));
  requires \valid(nonce + (0..7));
  requires keylen == 16 || keylen == 32;
  assigns *ctx,*key,nonce[0..7];
  ensures \result == 0 || \result == -1;
*/

int chacha_init(chacha_ctx *ctx,
                unsigned rounds,
                const uint8_t *key, uint32_t keylen,
                const uint8_t nonce[8])
{
    if (keylen == 32) {
        memcpy(ctx->state + 0, "expand 32-byte k", 16);
        //@ assert \valid((ctx->state+4)+(0..31));
        //@ assert \valid(key+(0..31));
        memcpy(ctx->state + 4, key, 32);
    }
    else if (keylen == 16) {
        memcpy(ctx->state + 0, "expand 16-byte k", 16);
        //@ assert \valid((ctx->state+4)+(0..15));
        //@ assert \valid(key+(0..15));
        memcpy(ctx->state + 4, key, 16);
        //@ assert \valid((ctx->state+8)+(0..15));
        //@ assert \valid(key+(0..15));
        memcpy(ctx->state + 8, key, 16);
    }
    else {
        return -1;
    }

    if ((rounds == 20) || (rounds == 12) || (rounds == 8)) {
        ctx->rounds = rounds;
    }
    else {
        return -1;
    }

    memset(ctx->state + 12, 0, 8);
    //@ assert \valid((ctx->state+14)+(14..22));
    //@ assert \valid(nonce+(0..7));
    memcpy(ctx->state + 14, nonce, 8);

    return 0;
}

/*@
  requires \valid(ctx);
  requires \valid(ctx->state+(0..15));
  requires ctx->rounds == 8 || ctx->rounds == 12 || ctx->rounds == 20;
  requires \valid_read(&(ctx->state[12]));
  requires \valid_read(&(ctx->state[13]));
  requires ctx->state[12] < INT_MAX;
  requires ctx->state[13] < INT_MAX;
  assigns *ctx;
*/

void chacha_keystream_bytes(chacha_ctx *ctx, void *x)
{
    _doubleround(x, ctx->state, ctx->rounds);

    ++ctx->state[12];
    if (ctx->state[12] == 0) {
        ++ctx->state[13];
    }
    //@ assert \forall unsigned i; 0 <= i < 16 ==> (ctx->state[i] == (ctx->state[i]) || ctx->state[i] == (ctx->state[i]) + (ctx->state[i+4]));
}

/*@
    requires \valid(ctx);
    requires \valid(c + (0..63));
    requires \valid(m + (0..63));
    assigns *c,*ctx,*m;
*/

void chacha_encrypt_bytes(chacha_ctx *ctx, const uint8_t *m, uint8_t *c)
{
    uint8_t x[64];

    chacha_keystream_bytes(ctx, x);
    for (unsigned i = 0; i < 64; ++i) {
        c[i] = m[i] ^ x[i];
    }
    //@ assert \forall integer i; 0 <= i < 64 ==> c[i] == (m[i] ^ x[i]);
}
