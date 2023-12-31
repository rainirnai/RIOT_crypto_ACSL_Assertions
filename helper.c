/*
 * Copyright (C) 2015 Nico von Geyso <nico.geyso@fu-berlin.de>
 * Copyright (C) 2015 René Kijewski <rene.kijewski@fu-berlin.de>
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

#include "helper.h"

/*@ requires \valid(block);
    requires L >= 0 && L <= 128;
    assigns *block;
*/


void crypto_block_inc_ctr(uint8_t block[16], int L)
{
    uint8_t *b = &block[15];

    for (int i = 0; i < L; ++i, --b) {
        if (++*b != 0) {
            break;
        }
    }
}

/*@
  requires len > 0;
  requires \valid(a+(0..len-1));
  requires \valid(b+(0..len-1));
  assigns *a,*b;
  ensures \result == 0 || \result == 1;
*/

int crypto_equals(const uint8_t *a, const uint8_t *b, size_t len)
{
    uint8_t diff = 0;

    for (size_t i = 0; i < len; ++i, ++a, ++b) {
        diff |= (*a ^ *b);
    }

    diff |= (diff >> 1) | (diff << 7);
    diff |= (diff >> 2) | (diff << 6);
    diff |= (diff >> 4) | (diff << 4);
    ++diff;

    return diff;
}

/* Compiler should not be allowed to optimize this */

void crypto_secure_wipe(void *buf, size_t len)
{
    volatile uint8_t *vbuf = (uint8_t *)buf;
    //@ assert \valid(vbuf);
    
    for (size_t i = 0; i < len; i++) {
        vbuf[i] = 0;
    }
    //@ assert \forall integer i; 0 <= i < len ==> vbuf[i] == 0;
}
