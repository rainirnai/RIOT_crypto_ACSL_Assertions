/*
 * Copyright (C) 2015 Freie Universität Berlin
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/*
 * @ingroup sys_crypto
 * @{
 * @file   ciphers.c
 * @author Nico von Geyso <nico.geyso@fu-berlin.de>
 * @}
 */

#include <string.h>
#include <stdio.h>
#include "ciphers.h"

/*@ requires \valid(cipher);
    requires \valid(cipher_id);
    requires \valid(key);
    requires key_size > 0 && key_size <= 32;
    assigns *cipher;
    ensures \result == CIPHER_INIT_SUCCESS || \result == CIPHER_ERR_BAD_CONTEXT_SIZE || \result == CIPHER_ERR_INVALID_KEY_SIZE;
*/

int cipher_init(cipher_t *cipher, cipher_id_t cipher_id, const uint8_t *key,
                uint8_t key_size)
{
    cipher->interface = cipher_id;
    return cipher->interface->init(&cipher->context, key, key_size);
}

/*@ requires \valid(cipher);
    requires cipher->interface != NULL;
    requires cipher->interface->encrypt != NULL;
    requires \valid(input);
    requires \valid(output);
    assigns *output;
    ensures \result == 1 || \result < 0;
   */

int cipher_encrypt(const cipher_t *cipher, const uint8_t *input,
                   uint8_t *output)
{
    return cipher->interface->encrypt(&cipher->context, input, output);
}

/*@
    requires \valid(cipher);
    requires \valid(input);
    requires \valid(cipher);
    assigns *output;
    ensures \result == 1 || \result < 0;
*/

int cipher_decrypt(const cipher_t *cipher, const uint8_t *input,
                   uint8_t *output)
{
    return cipher->interface->decrypt(&cipher->context, input, output);
}

/*@ requires \valid(cipher);
    ensures \result < 16;
*/
int cipher_get_block_size(const cipher_t *cipher)
{
    return cipher->interface->block_size;
}
