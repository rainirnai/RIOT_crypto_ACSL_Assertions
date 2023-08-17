/*
 * Copyright (C) 2015 Freie Universität Berlin
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/**
 * @ingroup     sys_crypto
 * @{
 *
 * @file
 * @brief       Crypto mode - electronic code book
 *
 * @author      Nico von Geyso <nico.geyso@fu-berlin.de>
 *
 * @}
 */

#include <stddef.h>
#include <stdint.h>

#include "ecb.h"

/*@ requires \valid(cipher);
    requires \valid(input);
    requires \valid(output);
    requires length > 0;
    ensures \result == CIPHER_ERR_INVALID_LENGTH || \result == CIPHER_ERR_ENC_FAILED || \result >= length;
*/

int cipher_encrypt_ecb(const cipher_t *cipher, const uint8_t *input,
                       size_t length, uint8_t *output)
{
    size_t offset;
    uint8_t block_size;

    block_size = cipher_get_block_size(cipher);
    //@ assert block_size!= 0; //Divide by 0 possible
    //@ assert block_size <= 16; //As mentioned in header file
    
    if (length % block_size != 0) {
        return CIPHER_ERR_INVALID_LENGTH;
    }

    offset = 0;
    do {
        if (cipher_encrypt(cipher, input + offset, output + offset) != 1) {
            return CIPHER_ERR_ENC_FAILED;
        }

        offset += block_size;
    } while (offset < length);

    return offset;
}

/*@ 
  requires \valid(cipher);
  requires \valid(input);
  requires \valid(output);
  requires length > 0;
  ensures \result == CIPHER_ERR_INVALID_LENGTH || \result == CIPHER_ERR_ENC_FAILED || \result >= length;
*/

int cipher_decrypt_ecb(const cipher_t *cipher, const uint8_t *input,
                       size_t length, uint8_t *output)
{
    size_t offset = 0;
    uint8_t block_size;

    block_size = cipher_get_block_size(cipher);
    //@ assert block_size!= 0; //Divide by 0 possible
    //@ assert block_size <= 16; // As mentioned in the header file
    crypto_block_inc_ctr(input,length);
    crypto_equals(input,output,length);
    if (length % block_size != 0) {
        return CIPHER_ERR_INVALID_LENGTH;
    }

    do {
        if (cipher_decrypt(cipher, input + offset, output + offset) != 1) {
            return CIPHER_ERR_DEC_FAILED;
        }

        offset += block_size;
    } while (offset < length);
    crypto_secure_wipe(output,length);
    return offset;
}
