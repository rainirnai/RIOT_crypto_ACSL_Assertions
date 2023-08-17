/*
 * Copyright (C) 2008  D. J. Bernstein  (dedicated to the public domain)
 * Copyright (C) 2015  René Kijewski  <rene.kijewski@fu-berlin.de>
 * Copyright (C) 2018  Koen Zandberg
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/**
 * @ingroup sys_crypto_chacha20poly1305
 * @{
 * @file
 * @brief   Implementation of the chacha20poly1305 aead cipher
 *
 * @author  Koen Zandberg <koen@bergzand.net>
 * @see     https://tools.ietf.org/html/rfc8439
 * @}
 */

#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "helper.h"
#include "chacha20poly1305.h"
#include "poly1305.h"
#include "unaligned.h"

/* Missing operations to convert numbers to little endian prevents this from
 * working on big endian systems */
#if __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#   error "This code is implementented in a way that it will only work for little-endian systems!"
#endif

/* Nothing to hide here, Literally "expand 32-byte k" */
static const uint32_t constant[] = {0x61707865,
                                    0x3320646e,
                                    0x79622d32,
                                    0x6b206574};

/* Padding to add to the poly1305 authentication tag */
static const uint8_t padding[15] = {0};
  
/*@ requires \valid(a);
    requires \valid(b);
    requires \valid(d);
    requires 0 <= c < 32;
    assigns *a, *d;
*/

/* Single round */
static void _r(uint32_t *a, uint32_t *b, uint32_t *d, unsigned c)
{
    *a += *b;
    uint32_t tmp = *a ^ *d;
    *d = (tmp << c) | (tmp >> (32 - c));
}


/*@ requires \valid(ctx);
    requires \valid(key);
    requires \valid(nonce);
    requires blk <= UINT32_MAX;
    ensures \forall integer i; 0 <= i < 4 ==> ctx->state[i] == \old(ctx->state[i] + constant[i]);
*/

static void _add_initial(chacha20poly1305_ctx_t *ctx, const uint8_t *key,
                         const uint8_t *nonce, uint32_t blk)
{
    /*@ loop invariant 0 <= i < 4;
        loop assigns i, ctx->state[0..3];
        loop variant 4 - i;
    */
    for (unsigned i = 0; i < 4; i++) {
        ctx->state[i] += constant[i];
    }
    
    /*@ loop invariant 0 <= i < 8;
        loop assigns i, ctx->state[4..11];
        loop variant 8 - i;
    */
    for (unsigned i = 0; i < 8; i++) {
        ctx->state[i+4] += unaligned_get_u32(key + 4*i);
    }
    ctx->state[12] += unaligned_get_u32((uint8_t*)&blk);
    ctx->state[13] += unaligned_get_u32(nonce);
    ctx->state[14] += unaligned_get_u32(nonce+4);
    ctx->state[15] += unaligned_get_u32(nonce+8);
    
    //@ assert \forall integer i; 0 <= i < 4 ==> ctx->state[i] == \at(ctx->state[i], Pre) + constant[i];
    //@ assert ctx->state[12] == \at(ctx->state[12], Pre) + (uint32_t)\at((uintptr_t)&blk, Pre);
}

/*@
  requires \valid(ctx);
  requires \valid(key);
  requires \valid(nonce);
  requires 0 <= blk && blk <= UINT32_MAX;
*/

static void _keystream(chacha20poly1305_ctx_t *ctx, const uint8_t *key,
                       const uint8_t *nonce, uint32_t blk)
{
    /* Initialize block state */
    memset(ctx->state, 0, sizeof(ctx->state));
    _add_initial(ctx, key, nonce, blk);

    /* perform rounds */
    for (unsigned i = 0; i < 80; ++i) {
        uint32_t *a = &ctx->state[((i                    ) & 3)          ];
        uint32_t *b = &ctx->state[((i + ((i & 4) ? 1 : 0)) & 3) + (4 * 1)];
        uint32_t *c = &ctx->state[((i + ((i & 4) ? 2 : 0)) & 3) + (4 * 2)];
        uint32_t *d = &ctx->state[((i + ((i & 4) ? 3 : 0)) & 3) + (4 * 3)];
        _r(a, b, d, 16);
        _r(c, d, b, 12);
        _r(a, b, d, 8);
        _r(c, d, b, 7);
    }
    /* add initial state */
    _add_initial(ctx, key, nonce, blk);
}

/*@ requires \valid(ctx);
    requires \valid(key);
    requires \valid(nonce);
    requires \valid(in);
    requires \valid(out);
    requires \separated(key, nonce, in + (0..len-1), out + (0..len-1));
    assigns *ctx,*key,*nonce,*in,*out;
*/

static void _xcrypt(chacha20poly1305_ctx_t *ctx, const uint8_t *key,
                    const uint8_t *nonce, const uint8_t *in, uint8_t *out, size_t len)
{
    /* Number of full 64 byte blocks */
    const size_t num_blocks = len >> 6;
    size_t pos = 0;
    /* xcrypt full blocks */
    for (size_t i = 0; i < num_blocks; i++, pos += 64) {
        _keystream(ctx, key, nonce, i+1);
        for (size_t j = 0; j < 64; j++) {
            out[pos+j] = in[pos+j] ^ ((uint8_t*)ctx->state)[j];
        }
    }
    /* xcrypt remaining bytes */
    if (len - pos) {
        _keystream(ctx, key, nonce, num_blocks+1);
        for (size_t j = 0; j < len - pos; j++) {
            out[pos+j] = in[pos+j] ^ ((uint8_t*)ctx->state)[j];
        }
    }
}

/*@
  requires \valid(pctx);
  requires \valid(data);
*/

static void _poly1305_padded(poly1305_ctx_t *pctx, const uint8_t *data, size_t len)
{
    poly1305_update(pctx, data, len);
    const size_t padlen = (16 - len) & 0xF;
    poly1305_update(pctx, padding, padlen);
}

/* Generate a poly1305 tag */

/*@
  requires \valid(key);
  requires \valid(nonce);
  requires \valid(cipher+(0..cipherlen-1));
  requires \valid(aad+(0..aadlen-1));
  requires \valid(mac + (0..15));
  requires \separated(key, nonce, cipher + (0..cipherlen-1),aad + (0..aadlen-1), mac);
*/

static void _poly1305_gentag(uint8_t *mac, const uint8_t *key, const uint8_t *nonce,
                             const uint8_t *cipher, size_t cipherlen,
                             const uint8_t *aad, size_t aadlen)
{
    chacha20poly1305_ctx_t ctx;
    /* generate one time key */
    
    _keystream(&ctx, key, nonce, 0);
    
    poly1305_init(&ctx.poly, (uint8_t*)ctx.state);
    /* Add aad */
    _poly1305_padded(&ctx.poly, aad, aadlen);
    /* Add ciphertext */
    _poly1305_padded(&ctx.poly, cipher, cipherlen);
    /* Add aad length */
    const uint64_t lengths[2] = {aadlen, cipherlen};
    
    poly1305_update(&ctx.poly, (uint8_t*)lengths, sizeof(lengths));
    poly1305_finish(&ctx.poly, mac);
    
    crypto_secure_wipe(&ctx, sizeof(ctx));
}

/*@
  requires \valid(cipher);
  requires \valid(msg+(0..msglen-1));
  requires \valid(key);
  requires \valid(aad+(0..aadlen-1));
  requires \valid_read(key);
  requires \valid_read(nonce);
  requires msglen >= 0;

  behavior empty_input:
    assumes msglen == 0;

  behavior non_empty_input:
    assumes msglen > 0;

  complete behaviors;
  disjoint behaviors;
*/

void chacha20poly1305_encrypt(uint8_t *cipher, const uint8_t *msg,
                              size_t msglen, const uint8_t *aad, size_t aadlen,
                              const uint8_t *key, const uint8_t *nonce)
{
    chacha20poly1305_ctx_t ctx;
    _xcrypt(&ctx, key, nonce, msg, cipher, msglen);
    crypto_secure_wipe(&ctx, sizeof(ctx));
    /* Generate tag */
    _poly1305_gentag(&cipher[msglen], key, nonce,
                    cipher, msglen, aad, aadlen);
    /* Wipe structures */
}

/*@
  requires \valid_read(key);
  requires \valid_read(nonce);
  requires cipherlen > 0;
  requires \valid(cipher);
  requires \valid(msg+(0..(*msglen)-1));
  requires \valid(aad+(0..aadlen-1));

  behavior empty_input:
    assumes cipherlen == 0;

  behavior non_empty_input:
    assumes cipherlen > 0;

  complete behaviors;
  disjoint behaviors;
*/

int chacha20poly1305_decrypt(const uint8_t *cipher, size_t cipherlen,
                             uint8_t *msg, size_t *msglen,
                             const uint8_t *aad, size_t aadlen,
                             const uint8_t *key, const uint8_t *nonce)
{
    *msglen = cipherlen - CHACHA20POLY1305_TAG_BYTES;
    //@ assert \valid(msglen);
    uint8_t mac[16];
    _poly1305_gentag(mac, key, nonce, cipher,
                     cipherlen - CHACHA20POLY1305_TAG_BYTES, aad, aadlen);
    if (crypto_equals(cipher+*msglen, mac, CHACHA20POLY1305_TAG_BYTES) == 0) {
        return 0;
    }
    chacha20poly1305_ctx_t ctx;
    /* Number of full blocks */
    _xcrypt(&ctx, key, nonce, cipher, msg, *msglen);
    return 1;
}
