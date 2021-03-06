#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

#include "EverCrypt.h"
#include "quic_provider.h"

#ifndef CDECL
  #if _WIN32
    #define CDECL __cdecl
  #else
    #define CDECL
  #endif
#endif

void dump(const unsigned char buffer[], size_t len)
{
  size_t i;
  for(i=0; i<len; i++) {
    printf("%02x",buffer[i] & 0xFF);
    if (i % 32 == 31 || i == len-1) printf("\n");
  }
}

void check_result(const char* testname, const unsigned char *actual, const unsigned char *expected, uint32_t length)
{
    for (uint32_t i=0; i<length; ++i) {
        if (actual[i] != expected[i]) {
            printf("FAIL %s:  actual 0x%2.2x mismatch with expected 0x%2.2x at offset %u\n",
              testname, actual[i], expected[i], i);
	    printf("Expected:\t"); dump(expected, length);
	    printf("Actual:\t"); dump(actual, length);
            exit(1);
        }
    }
}

// Older coverage tests
void coverage(void)
{
  printf("==== coverage ====\n");

  unsigned char hash[64] = {0};
  unsigned char input[1] = {0};
  printf("SHA256('') =\n");
  quic_crypto_hash(TLS_hash_SHA256, hash, input, 0);
  dump(hash, 32);
  assert(!memcmp(hash,"\xe3\xb0\xc4\x42\x98\xfc\x1c\x14\x9a\xfb\xf4\xc8\x99\x6f\xb9\x24\x27\xae\x41\xe4\x64\x9b\x93\x4c\xa4\x95\x99\x1b\x78\x52\xb8\x55",32));
  
  printf("\nSHA384('') = \n");
  quic_crypto_hash(TLS_hash_SHA384, hash, input, 0);
  dump(hash, 48);
  assert(!memcmp(hash, "\x38\xb0\x60\xa7\x51\xac\x96\x38\x4c\xd9\x32\x7e\xb1\xb1\xe3\x6a\x21\xfd\xb7\x11\x14\xbe\x07\x43\x4c\x0c\xc7\xbf\x63\xf6\xe1\xda\x27\x4e\xde\xbf\xe7\x6f\x65\xfb\xd5\x1a\xd2\xf1\x48\x98\xb9\x5b", 48));

  printf("\nSHA512('') = \n");
  quic_crypto_hash(TLS_hash_SHA512, hash, input, 0);
  dump(hash, 64);
  assert(!memcmp(hash, "\xcf\x83\xe1\x35\x7e\xef\xb8\xbd\xf1\x54\x28\x50\xd6\x6d\x80\x07\xd6\x20\xe4\x05\x0b\x57\x15\xdc\x83\xf4\xa9\x21\xd3\x6c\xe9\xce\x47\xd0\xd1\x3c\x5d\x85\xf2\xb0\xff\x83\x18\xd2\x87\x7e\xec\x2f\x63\xb9\x31\xbd\x47\x41\x7a\x81\xa5\x38\x32\x7a\xf9\x27\xda\x3e", 64));

  unsigned char *key = (unsigned char *)"Jefe";
  unsigned char *data = (unsigned char *)"what do ya want for nothing?";

  printf("\nHMAC-SHA256('Jefe', 'what do ya want for nothing?') = \n");
  quic_crypto_hmac(TLS_hash_SHA256, hash, key, 4, data, 28);
  dump(hash, 32);
  assert(memcmp(hash, "\x5b\xdc\xc1\x46\xbf\x60\x75\x4e\x6a\x04\x24\x26\x08\x95\x75\xc7\x5a\x00\x3f\x08\x9d\x27\x39\x83\x9d\xec\x58\xb9\x64\xec\x38\x43", 32) == 0);

  printf("\nHMAC-SHA384('Jefe', 'what do ya want for nothing?') = \n");
  quic_crypto_hmac(TLS_hash_SHA384, hash, key, 4, data, 28);
  dump(hash, 48);
  assert(memcmp(hash, "\xaf\x45\xd2\xe3\x76\x48\x40\x31\x61\x7f\x78\xd2\xb5\x8a\x6b\x1b\x9c\x7e\xf4\x64\xf5\xa0\x1b\x47\xe4\x2e\xc3\x73\x63\x22\x44\x5e\x8e\x22\x40\xca\x5e\x69\xe2\xc7\x8b\x32\x39\xec\xfa\xb2\x16\x49", 48) == 0);

  printf("\nHMAC-SHA512('Jefe', 'what do ya want for nothing?') = \n");
  quic_crypto_hmac(TLS_hash_SHA512, hash, key, 4, data, 28);
  dump(hash, 64);
  assert(memcmp(hash, "\x16\x4b\x7a\x7b\xfc\xf8\x19\xe2\xe3\x95\xfb\xe7\x3b\x56\xe0\xa3\x87\xbd\x64\x22\x2e\x83\x1f\xd6\x10\x27\x0c\xd7\xea\x25\x05\x54\x97\x58\xbf\x75\xc0\x5a\x99\x4a\x6d\x03\x4f\x65\xf8\xf0\xe6\xfd\xca\xea\xb1\xa3\x4d\x4a\x6b\x4b\x63\x6e\x07\x0a\x38\xbc\xe7\x37", 64) == 0);

  unsigned char *salt = (unsigned char *)"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c";
  unsigned char *ikm = (unsigned char *)"\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b";
  unsigned char *info = (unsigned char *)"\xf0\xf1\xf2\xf3\xf4\xf5\xf6\xf7\xf8\xf9";

  printf("\nprk = HKDF-EXTRACT-SHA256('0x000102030405060708090a0b0c', '0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b')\n");
  quic_crypto_hkdf_extract(TLS_hash_SHA256, hash, salt, 13, ikm, 22);
  dump(hash, 32);

  unsigned char prk[32] = {0};
  memcpy(prk, hash, 32);
  dump(prk, 32);

  unsigned char okm[42] = {0};
  printf("\nokm = HKDF-EXPAND-SHA256(prk, '0xf0f1f2f3f4f5f6f7f8f9', 42)\n");
  if(!quic_crypto_hkdf_expand(TLS_hash_SHA256, okm, 42, prk, 32, info, 10))
  {
    printf("Failed to call HKDF-expand\n");
    exit(1);
  }
  dump(okm, 42);

  quic_secret s = { .hash = TLS_hash_SHA256, .ae = TLS_aead_AES_128_GCM };
  memcpy(s.secret, hash, 32);
  quic_crypto_tls_derive_secret(&s, &s, "EXPORTER-QUIC server 1-RTT Secret");

  quic_key* k;
  if(!quic_crypto_derive_key(&k, &s))
  {
    printf("Failed to derive key\n");
    exit(1);
  }

  unsigned char cipher[128];
  printf("\nAES-128-GCM encrypt test:\n");
  quic_crypto_encrypt(k, cipher, 0, salt, 13, data, 28);
  dump(cipher, 28+16);
  assert (quic_crypto_decrypt(k, hash, 0, salt, 13, cipher, 28+16) == 1);
  if(memcmp(hash, data, 28) != 0)
  {
    printf("Roundtrip decryption failed.\n");
    exit(1);
  }
  assert(quic_crypto_decrypt(k, hash, 1, salt, 13, cipher, 28+16) == 0);
  assert(quic_crypto_decrypt(k, hash, 0, salt, 12, cipher, 28+16) == 0);
  assert(quic_crypto_decrypt(k, hash, 0, salt, 13, cipher+1, 27+16) == 0);

  unsigned char *expected_pnmask = (unsigned char*)"\xad\x2e\x76\x94\x51";
  unsigned char pnmask[5];

  if(quic_crypto_hp_mask(k, cipher, pnmask))
  {
    printf("PN encryption mask:\n");
    dump(pnmask, 5);
    check_result("PN encryption mask", pnmask, expected_pnmask, sizeof(pnmask));
  } else {
    printf("PN encryption failed.\n");
    exit(1);
  }

  if(quic_crypto_decrypt(k, hash, 0, salt, 13, cipher, 28+16)) {
    printf("DECRYPT SUCCESS: \n");
    dump(hash, 28);
  } else {
    printf("DECRYPT FAILED.\n");
    exit(1);
  }

  quic_crypto_free_key(k);

  s.hash = TLS_hash_SHA256;
  s.ae = TLS_aead_CHACHA20_POLY1305;

  if(!quic_crypto_derive_key(&k, &s))
  {
    printf("Failed to derive key\n");
    exit(1);
  }

  printf("\nCHACHA20-POLY1305 encrypt test:\n");
  quic_crypto_encrypt(k, cipher, 0x29e255a7, salt, 13, data, 28);
  dump(cipher, 28+16);

  expected_pnmask = (unsigned char*)"\xea\xe0\x0a\xd8\x60";
  if(quic_crypto_hp_mask(k, cipher, pnmask))
  {
    printf("PN encryption mask:\n");
    dump(pnmask, 5);
    check_result("PN encryption mask", pnmask, expected_pnmask, sizeof(pnmask));
  } else {
    printf("PN encryption failed.\n");
    exit(1);
  }

  if(quic_crypto_decrypt(k, hash, 0x29e255a7, salt, 13, cipher, 28+16)) {
    printf("DECRYPT SUCCESS: \n");
    dump(hash, 28);
  } else {
    printf("DECRYPT FAILED.\n");
  }

  quic_crypto_free_key(k);
  printf("==== PASS:  coverage ====\n\n\n");
}

//////////////////////////////////////////////////////////////////////////////


const uint64_t sn = 0x29;

#define ad_len      0x11
const unsigned char ad[ad_len] =
{0xff,0x00,0x00,0x4f,0xee,0x00,0x00,0x42,0x37,0xff,0x00,0x00,0x09,0x00,0x00,0x00};

#define plain_len 256
const unsigned char plain[plain_len] = {
0x12,0x00,0x40,0xda,0x16,0x03,0x03,0x00,0xd5,0x01,0x00,0x00,0xd1,0x03,0x03,0x5a,
0xa0,0x4e,0xf1,0x3b,0x74,0x7c,0x34,0xe6,0x74,0x05,0xc9,0x1f,0x0a,0x2a,0x5c,0x5d,
0x1f,0xf9,0x08,0x01,0x77,0xb5,0xe8,0x35,0x94,0x34,0x70,0xbd,0xdd,0x86,0xa5,0x00,
0x00,0x04,0x13,0x03,0x13,0x01,0x01,0x00,0x00,0xa4,0x00,0x1a,0x00,0x2c,0xff,0x00,
0x00,0x09,0x00,0x26,0x00,0x01,0x00,0x04,0x00,0x10,0x00,0x00,0x00,0x00,0x00,0x04,
0x00,0x04,0x00,0x00,0x00,0x02,0x00,0x04,0x00,0x00,0x00,0x21,0x00,0x08,0x00,0x04,
0x00,0x00,0x00,0x23,0x00,0x03,0x00,0x02,0x00,0x64,0x00,0x2b,0x00,0x03,0x02,0x7f,
0x17,0x00,0x33,0x00,0x26,0x00,0x24,0x00,0x1d,0x00,0x20,0x33,0xc5,0x86,0xee,0x6c
};

const unsigned char cipher_sha256_aes128[] = { // results_3_0
0xeb,0x75,0x99,0x58,0x97,0xe9,0xe6,0x03,0x42,0x16,0x44,0xc2,0xf3,0xbb,0xb6,0xce,
0xe2,0x24,0xeb,0x97,0xe1,0x6c,0x56,0xe9,0x4e,0x6d,0x0f,0xd8,0xff,0x51,0x70,0x11,
0x84,0x94,0x29,0x7f,0xf7,0x1c,0x2d,0x2e,0x08,0x4c,0xab,0xb8,0x69,0x23,0xf8,0x66,
0x9d,0x64,0x95,0x4b,0x9f,0x76,0x4e,0xed,0x75,0xf1,0x3c,0x2a,0xf0,0xcf,0x2f,0x60,
0xa7,0x78,0xa8,0xa8,0xba,0xf6,0x1d,0xc3,0x21,0x6f,0x2c,0x4d,0x48,0x4b,0x50,0xc4,
0xdb,0xeb,0x88,0xaa,0x7c,0x28,0x90,0x65,0x0c,0xdf,0x83,0x38,0x54,0x46,0x83,0x5d,
0x09,0x49,0xbb,0x9c,0xfb,0xd8,0xba,0xd4,0x63,0x04,0x64,0xcb,0x85,0xf8,0x58,0x89,
0x4b,0x3a,0x79,0x08,0x52,0xe3,0x96,0x61,0x2c,0x45,0xea,0x0a,0x3f,0x31,0x98,0x13,
0x25,0xb7,0xd3,0x95,0x95,0x30,0xcd,0x59,0x73,0xab,0xae,0x40,0x11,0x73,0x8f,0xee,
0x95,0x3d,0x1f,0xf4,0x22,0xeb,0x94,0xea,0x7d,0xdf,0x76,0xad,0x77,0x48,0x97,0x8d,
0x4e,0x6a,0xa2,0x5c,0x12,0x1d,0x85,0x6b,0x09,0xf2,0x4c,0xb3,0xcd,0xfb,0xd7,0xf4,
0x0a,0x6b,0x95,0x4c,0x8d,0xbe,0x08,0x7b,0x56,0x89,0xde,0x81,0x7c,0xcb,0x2f,0x55,
0x45,0x8a,0x99,0xe3,0x52,0x34,0x85,0x2a,0x9b,0x62,0x48,0xa9,0xb7,0x0a,0x6e,0xf5,
0x0e,0x72,0x83,0x86,0x9a,0xdb,0x5b,0x57,0x07,0x5f,0xd2,0xa1,0x3b,0x3a,0x2a,0xf7,
0x68,0xd2,0xe1,0xae,0x39,0x1a,0x7b,0xfa,0x08,0x3b,0x73,0xa8,0x48,0xac,0xc0,0xf7,
0x5b,0xc8,0x7b,0x54,0x03,0x7f,0x71,0xdb,0xd7,0xe1,0x67,0x59,0x08,0x9c,0xea,0x18,
0x76,0x8e,0x42,0x79,0xd9,0x81,0x72,0x34,0xa9,0x5d,0x82,0x1d,0xf2,0x17,0x32,0x03,
};

const unsigned char cipher_sha384_aes128[] = { // results_4_0
0x50,0xec,0x16,0x1d,0x01,0xb6,0xd7,0x90,0xdd,0x02,0x40,0xac,0x9b,0xc9,0xe3,0x5b,
0x7d,0xdd,0xa8,0x79,0xe5,0x2b,0x8c,0xbc,0x7c,0x2e,0x5f,0xeb,0xde,0x52,0x5b,0xbc,
0x30,0x12,0x28,0x12,0x9e,0x82,0x53,0x9c,0xe3,0x06,0x8d,0x31,0xea,0xf4,0x57,0x67,
0xd7,0xf9,0x96,0x76,0x38,0x65,0x21,0xb7,0x46,0x10,0xcc,0xee,0x57,0x1e,0x5a,0x2d,
0xf1,0x92,0x91,0x5f,0xa0,0x67,0x2f,0x75,0xfe,0xb8,0x18,0x23,0x46,0xe1,0x48,0xf6,
0x7d,0xae,0x55,0xe4,0x6d,0xff,0xe6,0x88,0x81,0xbd,0x59,0x05,0xab,0x61,0x07,0x92,
0xff,0x38,0xaa,0xd6,0x03,0x0d,0x83,0x38,0x59,0x4e,0x68,0x94,0xe2,0x19,0xdc,0xf0,
0xbc,0x8f,0x9b,0xf2,0xb1,0x7f,0xa8,0xc6,0xae,0x47,0xc8,0x9b,0x75,0x32,0xe3,0xe2,
0x83,0xe2,0xa0,0x44,0x04,0xe5,0xd3,0x7c,0x98,0xbd,0xc2,0x65,0x3d,0xde,0x56,0x97,
0xdf,0x6a,0x2d,0xa8,0x1d,0xc3,0xf3,0xd2,0xf9,0x9b,0x03,0x51,0x65,0xc4,0x05,0xcf,
0x53,0x70,0x0e,0xab,0x53,0xa4,0x9f,0x4c,0x65,0xc0,0x41,0xdd,0x58,0xe1,0xb0,0xb6,
0xe9,0xd7,0x02,0xca,0xa3,0x16,0x3b,0x84,0x10,0x3e,0x45,0xd3,0x06,0x2b,0x16,0xf6,
0x47,0xbd,0xe9,0x5c,0x79,0x97,0xf4,0x52,0x96,0xcc,0x85,0xd9,0x89,0xcb,0x82,0x23,
0x6f,0x80,0xcc,0xc1,0xfc,0x1b,0xbd,0x42,0x56,0xf8,0x01,0xef,0x64,0xb5,0x10,0x25,
0x29,0x35,0xbf,0xf6,0x33,0xe2,0x1f,0x49,0xbf,0xf9,0x87,0x69,0x8b,0x0b,0x0c,0x3a,
0xe5,0x19,0xf9,0xe3,0xae,0xee,0x1c,0x1a,0x67,0x7e,0x8d,0xc9,0xf5,0x44,0x4e,0x27,
0x39,0x72,0x11,0x8c,0x72,0x76,0xdc,0xcd,0x77,0x27,0xcc,0x39,0xba,0xe6,0xc6,0x39,
};

const unsigned char cipher_sha512_aes128[] = { // results_5_0
0x4a,0x80,0x31,0xbd,0xeb,0x68,0x92,0x1d,0xd5,0xbd,0x50,0x90,0x95,0x08,0x74,0xdb,
0xd8,0xe3,0xd0,0x86,0x4b,0x28,0x71,0xdb,0x59,0xbe,0x46,0x96,0x54,0xe6,0xe9,0x44,
0xa3,0x34,0x78,0x6b,0x24,0x39,0x03,0x40,0xcf,0xa8,0xa8,0x0b,0x85,0xdd,0xdb,0x09,
0xf4,0x72,0x54,0x1a,0x1f,0xc5,0x3b,0xee,0x4d,0xc8,0x5c,0x64,0xb7,0x54,0x02,0xff,
0xa6,0x9d,0xf3,0x6d,0x2d,0xa5,0x52,0xdc,0xfc,0xe2,0x38,0xc8,0xd0,0xc5,0x92,0x0f,
0x05,0x92,0xf2,0xd0,0xbf,0xc6,0xb1,0xc1,0xf9,0xcc,0x19,0x90,0xfa,0x1e,0x1c,0x35,
0x64,0xff,0xed,0x4c,0x28,0x1f,0xce,0x31,0xfa,0x55,0xab,0xa5,0xac,0xbe,0x03,0x98,
0x68,0x71,0xcd,0xdc,0x03,0x93,0xd0,0xec,0x90,0xf6,0xe9,0xb7,0xbd,0x41,0xac,0x4a,
0xd0,0x4d,0x80,0x8b,0xe5,0x2a,0x76,0x0b,0xc2,0xfa,0xc6,0x52,0xac,0xb1,0x6d,0xd4,
0x8d,0xf3,0x5b,0x06,0x51,0x89,0x0a,0xad,0xaf,0x21,0xeb,0x9f,0x77,0x6a,0x6e,0x76,
0x47,0x58,0xb0,0xb2,0xa5,0xb8,0x7d,0x56,0x7a,0x85,0x9c,0x72,0xc2,0x28,0x1d,0x8a,
0x87,0x89,0x68,0xca,0x8d,0x4d,0x3c,0x5c,0xff,0xbf,0x5c,0x1c,0xf3,0xfc,0xc0,0x47,
0xa7,0x2a,0xbd,0x74,0x85,0x80,0xee,0x0e,0xec,0xfc,0x62,0x5d,0x55,0xa2,0x7d,0xb0,
0xf6,0x4b,0xfb,0xdd,0x36,0x95,0xcf,0xc8,0x36,0xbd,0x14,0x2e,0x6b,0xe3,0x5a,0x70,
0x8d,0x81,0xd6,0x30,0x5a,0x81,0x6b,0x0b,0xff,0xd7,0x73,0xa1,0x19,0xc2,0x22,0xc0,
0x40,0x2f,0xe4,0x5c,0x8b,0x6d,0xa4,0xd4,0xba,0x95,0x5d,0x58,0x80,0x92,0xab,0x00,
0x66,0x93,0x6a,0x5d,0xac,0xac,0x19,0x47,0x57,0xbc,0x3c,0x82,0x5a,0x59,0x1f,0x5a
};

const unsigned char cipher_sha256_aes256[] = { // results_3_1
0x42,0x1a,0x4f,0xa7,0x9d,0x95,0xe5,0x60,0xc0,0x7f,0xcb,0x02,0xef,0x64,0xb8,0x3c,
0xf4,0x30,0xd1,0xf8,0x9b,0xab,0xa6,0x94,0x47,0xbb,0x6b,0x30,0x35,0xc3,0xe7,0x83,
0x6c,0xd6,0x4c,0x99,0xeb,0xca,0x59,0xb4,0x93,0x21,0x6b,0x0b,0x22,0x69,0x78,0x8c,
0xe7,0xdc,0xbd,0x36,0x9e,0x95,0x10,0x8a,0x46,0x86,0xc2,0x3e,0xed,0x13,0xe7,0x3f,
0xf4,0x64,0xc8,0x6f,0xb0,0xb2,0x98,0x6b,0xbc,0x14,0x1d,0xfb,0x19,0x89,0x92,0x7a,
0xa9,0x0d,0xb5,0xe3,0x86,0x6b,0x7c,0x05,0x5a,0x51,0x59,0x9d,0xae,0x11,0x6d,0x65,
0xfc,0x2e,0x3f,0x45,0x3e,0xf3,0xbd,0x06,0x20,0x41,0xe6,0xb7,0x5b,0x04,0xf5,0xc8,
0x4c,0x25,0x75,0x9e,0x7d,0x7b,0xf8,0x69,0xa1,0xb4,0x7a,0x82,0xc8,0x1c,0xaa,0xec,
0x57,0x94,0xcc,0x7e,0x32,0x32,0xe5,0xb6,0x52,0x2e,0x05,0x99,0xa7,0x0f,0x0f,0x57,
0x9e,0xf7,0xeb,0x3f,0x09,0xe3,0x17,0xeb,0x38,0x4c,0x1e,0xd9,0x4e,0xde,0x38,0x74,
0x89,0x3a,0x61,0xc9,0x2a,0x07,0xef,0xdf,0x08,0xc4,0x43,0xcd,0xcb,0xe5,0x5b,0x41,
0xba,0xfa,0x8e,0x3c,0x85,0x58,0x30,0x08,0x86,0x13,0x94,0x6a,0x7e,0xee,0xa6,0x88,
0xd2,0xf8,0x42,0x57,0x9e,0x94,0x4c,0x33,0x02,0xab,0xa7,0xa6,0x37,0x98,0x3a,0xc7,
0x9e,0x48,0x2d,0xd5,0x1f,0xad,0x66,0xe5,0x9a,0x56,0xaa,0xfb,0xc9,0x43,0xf8,0xf4,
0x41,0x4e,0xb1,0xec,0x30,0x54,0xfa,0x48,0x8f,0xcc,0x22,0x8d,0x7c,0xb8,0xbd,0xa8,
0x9d,0xa4,0x02,0x1b,0x7c,0x9c,0xc2,0x0d,0x7a,0x8f,0x62,0x47,0x68,0xaa,0xd3,0xe9,
0x9e,0xa5,0x2a,0xb2,0xc1,0xc4,0x16,0xd0,0x00,0xfb,0xc2,0x9d,0x89,0xef,0x91,0xaf,
};

const unsigned char cipher_sha384_aes256[] = { // results_4_1
0x84,0x96,0x4a,0x6e,0xe3,0xcd,0x2f,0x5d,0xac,0xc7,0x04,0x58,0x22,0xaf,0xb9,0x3d,
0xc0,0x4d,0xd9,0xe2,0x93,0xf6,0x3b,0x9b,0x60,0xf4,0x2a,0xb3,0x61,0xf7,0x7b,0xde,
0x3e,0x32,0x75,0xe9,0xe2,0xf5,0xf2,0x3d,0xc7,0x64,0x1c,0xcb,0x59,0x0e,0x47,0x2f,
0x8f,0xdf,0xa9,0xdc,0x14,0x7b,0x19,0x0f,0x3e,0x2a,0x30,0x94,0xe1,0x87,0xa2,0x75,
0x29,0x58,0x65,0x22,0xf2,0xf5,0x17,0xa7,0x3e,0x8e,0x52,0x01,0xd8,0xa9,0x36,0xfa,
0x0a,0xae,0xb6,0x5b,0xa5,0x22,0x97,0x75,0xee,0xb6,0x15,0xc1,0x0e,0xa7,0xba,0x16,
0x05,0x05,0x4c,0x52,0xf0,0x23,0x1c,0xcb,0x1e,0x42,0x9c,0xe6,0x01,0xb2,0x0c,0x58,
0x4b,0xcc,0x18,0x10,0x7c,0x6d,0xa4,0xf5,0x92,0x7a,0xe8,0x96,0x57,0x47,0xc2,0x5e,
0xf5,0x16,0x25,0x08,0x13,0xe3,0x3b,0x69,0x68,0xbf,0xfe,0x92,0x96,0x85,0x8b,0xe1,
0xac,0x4e,0x46,0xaf,0x05,0xd4,0xc6,0x7a,0x68,0x98,0x2c,0xff,0xaf,0x6d,0x16,0x85,
0xf4,0xd4,0x75,0xce,0x6c,0xa2,0xcb,0xb1,0x78,0x76,0x4e,0xec,0x75,0xb4,0x00,0x5f,
0xf9,0x8e,0xfe,0x34,0x26,0x07,0xfe,0x2b,0x46,0x9b,0xb4,0x3d,0xb8,0x9e,0x7b,0x97,
0x3e,0x18,0x22,0x45,0xe1,0xa3,0x60,0x32,0x41,0x5d,0xf2,0x4c,0x08,0xec,0xcd,0xfa,
0xad,0x1e,0x87,0x95,0x33,0xc5,0x52,0xdc,0x17,0xe0,0x00,0x9d,0xe4,0xa2,0x0f,0x8a,
0xd7,0xba,0x4c,0x7d,0xe4,0x7b,0xc9,0xbd,0x02,0xc0,0xe5,0x98,0xa2,0x5a,0xa2,0xf6,
0xe8,0x7d,0xc9,0x44,0x5a,0x5d,0xa6,0x57,0x59,0x26,0x38,0x59,0xce,0x36,0x7c,0x0e,
0x1a,0xc8,0x04,0x5b,0x52,0xeb,0x33,0x48,0x0f,0x9b,0x7f,0x84,0x83,0x8e,0xda,0x6b,
};

const unsigned char cipher_sha512_aes256[] = { // results_5_1
0x74,0x38,0xde,0x84,0x71,0x60,0x09,0x8f,0xac,0x60,0x4c,0x6d,0x07,0x9b,0x27,0x38,
0xd3,0x56,0x88,0x57,0x0c,0x47,0xbb,0xf1,0x9f,0x7e,0x35,0xb9,0xa2,0x3c,0xfe,0x30,
0xff,0x44,0xcc,0xdc,0x07,0x70,0x59,0xe2,0xca,0xc0,0x9b,0x37,0xf9,0x92,0x82,0x64,
0xa5,0x52,0x4b,0x78,0x17,0x4e,0xbd,0xa4,0xf2,0x16,0x48,0xb8,0x25,0x46,0x2e,0xef,
0x7a,0xae,0xb1,0x00,0x55,0xd8,0x1d,0xfa,0xa9,0xfd,0x2d,0xdb,0x11,0xf9,0x15,0x02,
0xcf,0xd1,0x0b,0xc0,0x61,0x93,0x3a,0x0d,0x8c,0x95,0x45,0x4e,0xbc,0x76,0x9e,0x23,
0xb7,0x7f,0xa0,0x00,0x62,0x43,0x44,0x2e,0xcf,0xb0,0x64,0x9c,0xce,0x95,0xd0,0x1a,
0x7c,0xb0,0xa0,0x79,0x74,0xf3,0x92,0x1a,0x58,0xff,0x09,0x71,0x3d,0xf5,0x39,0x06,
0x75,0x05,0xbf,0x76,0x89,0x86,0x57,0x7e,0x58,0x5f,0x3b,0xae,0xa7,0xff,0x39,0x2b,
0x74,0x52,0xc6,0x27,0x07,0x7a,0x74,0x0a,0x5d,0x39,0xc3,0x4d,0xf2,0xec,0x4a,0x62,
0x92,0x86,0x7d,0xdc,0x48,0x5c,0xf8,0xe6,0xd2,0x21,0xe2,0x25,0xae,0x82,0x33,0x2f,
0xbc,0xfe,0xe1,0x0c,0x4e,0x38,0x05,0x47,0x06,0xb3,0xd1,0x45,0x1e,0x29,0x39,0x89,
0xe4,0x91,0x81,0xcb,0xbd,0xf5,0x1e,0x05,0x1c,0xed,0xc6,0x7f,0xa0,0x98,0x57,0x61,
0xc8,0x0d,0xf6,0xe7,0x7d,0xab,0x7b,0x85,0xd7,0xa4,0x84,0xd7,0x64,0xed,0xdb,0x7e,
0xd7,0x64,0x8b,0xe5,0x8c,0xd4,0x2b,0xb1,0x35,0x51,0x4d,0xbc,0x6e,0xe0,0x4e,0xa8,
0x1b,0x7a,0x58,0x3d,0xe0,0x82,0x7d,0xd9,0xbe,0xda,0xcc,0x25,0x97,0x07,0xcb,0x8b,
0xcb,0x5b,0x4a,0xd9,0x43,0xef,0xea,0xeb,0x62,0x61,0x56,0xd4,0xdb,0x23,0xf6,0x63,
};

const unsigned char cipher_sha256_chachapoly[] = { // results_3_2
0x35,0xa7,0x5b,0x35,0x0f,0x0f,0x5c,0x2a,0xcc,0xdf,0x9e,0x58,0xec,0xe3,0xfe,0x5a,
0x9d,0x87,0x19,0x86,0x65,0x24,0x2d,0x5d,0x9f,0x37,0x04,0x0d,0x8b,0x5e,0xe8,0x0d,
0x9c,0x22,0x74,0x15,0xdf,0x4d,0x95,0xed,0x20,0x91,0xe4,0xce,0x0a,0xbd,0x5b,0x57,
0x02,0xd8,0xd8,0xb9,0xc4,0xb3,0x21,0xe6,0x10,0xc6,0xcd,0x59,0xc5,0xd6,0x14,0x58,
0xf5,0xaf,0x57,0xb5,0x79,0x1f,0xc1,0x69,0xff,0xa8,0xd8,0x58,0x00,0x0e,0x0f,0x3d,
0xf4,0xcb,0xd4,0x21,0x9f,0x77,0x90,0xae,0x0e,0x16,0xed,0x96,0x71,0x15,0xeb,0x0a,
0x61,0x3e,0xfb,0xb1,0x4a,0xe7,0x74,0x65,0xfc,0x35,0x87,0x39,0xc6,0x7c,0x05,0xb9,
0x1c,0xf3,0xd4,0xd9,0xb5,0x72,0x14,0x9c,0xb3,0x91,0xbf,0x67,0xa1,0xa3,0x10,0x93,
0xb2,0xa9,0x07,0xf0,0x1e,0x0c,0xc5,0x1b,0x2f,0x0b,0x4e,0x55,0x93,0xb8,0x30,0x8e,
0xbf,0x7e,0x09,0xd2,0x28,0xbb,0x60,0xd6,0x98,0xd3,0xaf,0x60,0xa6,0xe1,0xc6,0x4f,
0x58,0x33,0x78,0xb5,0x55,0x1e,0xcc,0x4b,0x0c,0xe2,0x99,0x9b,0x2e,0xfe,0xa3,0x5e,
0x2c,0x44,0xe6,0xb3,0x26,0x6f,0x42,0x01,0xac,0xf2,0x40,0x17,0x06,0xc8,0xed,0x00,
0xec,0x2b,0xf6,0x08,0xd8,0x3e,0xf0,0xe0,0x3d,0xdb,0x2c,0xa0,0xbd,0xe3,0xf4,0xe8,
0x43,0x94,0xac,0x1b,0x01,0x20,0x2c,0x35,0x94,0x31,0x2b,0xe4,0xab,0x7f,0x05,0x8d,
0x9b,0x26,0x8d,0xdb,0xa2,0x05,0xe0,0x17,0xf0,0x3c,0x29,0x37,0xb7,0x13,0xd0,0x99,
0x2b,0x37,0x79,0xf1,0xff,0xca,0x4f,0x58,0xc5,0xbb,0x1a,0xbd,0x64,0xe0,0xd3,0xf3,
0x71,0xc8,0x4e,0x87,0xb8,0xe1,0xd2,0x84,0x61,0x25,0xcf,0xb2,0xcd,0x65,0xdc,0x91,
};

const unsigned char cipher_sha384_chachapoly[] = { // results_4_2
0xf8,0x27,0xdd,0x11,0x2b,0x84,0xeb,0x7d,0xb1,0x6f,0x35,0xcd,0x2d,0x15,0x76,0xad,
0x34,0x9f,0x9b,0x56,0xf2,0x52,0x30,0x13,0x93,0x33,0x25,0x9c,0x75,0x5e,0x3d,0x72,
0x6d,0x51,0xe5,0xf5,0xf9,0xd5,0x99,0x19,0x12,0x68,0x70,0x63,0x68,0x97,0xb0,0x5a,
0x6d,0x05,0x2e,0x7a,0xd8,0x25,0x98,0x25,0x81,0x94,0x1c,0x26,0x2e,0xfa,0x84,0x38,
0x0f,0xaf,0xd6,0xfb,0x06,0xf0,0x38,0xde,0x89,0x28,0x66,0xfa,0x2d,0x6b,0x8e,0xfa,
0x45,0xc1,0x00,0x4d,0xf4,0x31,0x05,0x80,0x38,0xdc,0xb6,0x78,0x1b,0x83,0xc0,0xf2,
0x7e,0xcf,0x19,0xec,0xb3,0xc3,0xd5,0x90,0xbf,0x77,0x36,0x55,0x62,0xba,0xfe,0xd0,
0xe4,0x5c,0xe0,0xf2,0x98,0x95,0xea,0x1e,0x54,0xdf,0xf4,0x65,0x70,0x09,0xfb,0x3a,
0x39,0x88,0xa6,0xf2,0xf5,0xb0,0xaa,0x79,0x4f,0x43,0x82,0x03,0xfd,0x61,0xbf,0x0d,
0x84,0x2e,0x22,0x81,0xab,0xeb,0x56,0xec,0xd4,0xe3,0x0d,0x41,0x9a,0xe8,0x95,0x4a,
0x1d,0xe9,0x7d,0xbb,0xe3,0xf8,0xd1,0x01,0x3a,0x22,0x00,0xea,0xc2,0x42,0x4d,0xe2,
0x3b,0x79,0xb6,0x1a,0x84,0x44,0x83,0x8e,0xb9,0x9b,0x27,0x47,0x1a,0x05,0x81,0x1c,
0x38,0x58,0xd4,0x59,0x03,0x5c,0x5d,0xe2,0x5f,0xff,0x57,0x1f,0xb5,0x85,0x9a,0x80,
0xa4,0xb9,0x0e,0x5c,0xcf,0xe4,0x6f,0x36,0xa6,0xa3,0x47,0x21,0xa6,0x95,0xcf,0xbe,
0x94,0xc2,0xd6,0x83,0x8d,0x16,0xa3,0x3a,0x11,0x5e,0xd7,0x1a,0x4d,0x25,0xd7,0xf6,
0x02,0x88,0x7f,0xb1,0x10,0x69,0x42,0xa5,0xb7,0x51,0x68,0x4e,0x84,0x45,0xe5,0xc9,
0x63,0x13,0x12,0x02,0x58,0x9b,0x44,0x1d,0x72,0x7a,0xf0,0xa9,0xc5,0x7a,0x10,0xec,
};

const unsigned char cipher_sha512_chachapoly[] = { // results_5_2
0x83,0x35,0xbd,0x12,0x80,0x6f,0x06,0x67,0x20,0x6b,0xfe,0x9c,0x91,0x9c,0x0a,0x61,
0x20,0xd9,0xe4,0x0f,0x64,0x1e,0x80,0x75,0x9b,0x7f,0xaa,0xb1,0xae,0x18,0x37,0xa3,
0x51,0x61,0x0b,0xb1,0x90,0x38,0x70,0xe8,0x18,0xc6,0x49,0xad,0x31,0xe2,0x22,0x69,
0xd4,0xca,0x1b,0x6e,0xd0,0x09,0x45,0xb5,0x34,0x01,0x83,0x59,0xdd,0xa7,0x19,0x30,
0x20,0xb5,0xf5,0xdf,0x2d,0xed,0xf6,0x03,0x3c,0x0c,0xc1,0x73,0x5a,0x20,0xc7,0x5d,
0x55,0x5a,0x88,0x1f,0x45,0xdb,0x01,0x5c,0xc7,0xd5,0x02,0x45,0x74,0xc8,0x2c,0xf6,
0xa5,0xb7,0xf7,0x98,0x79,0x7b,0xc3,0xd8,0xb7,0x0e,0x80,0x93,0x2b,0xa9,0x2f,0x45,
0x3d,0x38,0xf0,0x08,0x8a,0x3a,0xc7,0x6c,0xcf,0xaa,0x47,0xb3,0x2e,0x6a,0x08,0x23,
0xec,0x89,0x1e,0x12,0x29,0x27,0x1a,0xa5,0xe8,0xd0,0x5e,0x03,0xeb,0x85,0x32,0x60,
0x6c,0x98,0xf6,0x9d,0xc4,0x43,0x4d,0x10,0x69,0xe8,0x3d,0x7d,0x1c,0xb8,0xa9,0xd5,
0xbb,0xf9,0x12,0xeb,0x4e,0xe3,0xeb,0x54,0x99,0x14,0x9d,0x70,0x27,0xd1,0x71,0x75,
0x56,0xe9,0xb4,0xc9,0xcb,0xd4,0xf2,0x09,0x6f,0x9f,0x01,0xc6,0x10,0xf5,0x3a,0x0b,
0x1e,0xce,0xa3,0xb4,0x56,0x6a,0xad,0x77,0xfe,0xb6,0xda,0x69,0xe9,0x87,0xb2,0xc0,
0x1b,0x63,0x72,0x86,0xa5,0xd8,0x95,0x5e,0x74,0x3b,0x2c,0xdc,0x28,0x05,0x68,0x21,
0xad,0x04,0x86,0x06,0x2c,0x6b,0xe9,0x94,0xdc,0x0a,0xaf,0x69,0xd1,0xe8,0xc8,0xcc,
0xaf,0x86,0xa1,0x3a,0x91,0x64,0x9d,0x20,0x28,0xac,0x27,0xfa,0xec,0xc5,0x31,0xf6,
0x0c,0x65,0xf8,0x73,0x3d,0x33,0x21,0xdc,0xe2,0x10,0xd0,0x21,0x04,0x02,0x1e,0x1e,
};

struct testcombination {
    mitls_hash hash;
    mitls_aead ae;
    const unsigned char *expected_cipher;
} testcombinations[] = {
    // TLS_hash_MD5 and TLS_hash_SHA1 aren't supported by libquiccrypto

    { TLS_hash_SHA256, TLS_aead_AES_128_GCM, cipher_sha256_aes128 },
    { TLS_hash_SHA384, TLS_aead_AES_128_GCM, cipher_sha384_aes128 },
    { TLS_hash_SHA512, TLS_aead_AES_128_GCM, cipher_sha512_aes128 },

    { TLS_hash_SHA256, TLS_aead_AES_256_GCM, cipher_sha256_aes256 },
    { TLS_hash_SHA384, TLS_aead_AES_256_GCM, cipher_sha384_aes256 },
    { TLS_hash_SHA512, TLS_aead_AES_256_GCM, cipher_sha512_aes256 },

    { TLS_hash_SHA256, TLS_aead_CHACHA20_POLY1305, cipher_sha256_chachapoly },
    { TLS_hash_SHA384, TLS_aead_CHACHA20_POLY1305, cipher_sha384_chachapoly },
    { TLS_hash_SHA512, TLS_aead_CHACHA20_POLY1305, cipher_sha512_chachapoly },

    { 0, 0, NULL }
};

// map mitls_hash to a string name
const char *hash_to_name[] = {
    "TLS_hash_MD5",
    "TLS_hash_SHA1",
    "TLS_hash_SHA224",
    "TLS_hash_SHA256",
    "TLS_hash_SHA384",
    "TLS_hash_SHA512"
};

// map mitls_aead to a string name
const char *aead_to_name[] = {
    "TLS_aead_AES_128_GCM",
    "TLS_aead_AES_256_GCM",
    "TLS_aead_CHACHA20_POLY1305"
};

void dumptofile(FILE *fp, const char buffer[], size_t len)
{
  size_t i;
  for(i=0; i<len; i++) {
    fprintf(fp, "0x%2.2x,", (unsigned char)buffer[i]);
    if (i % 16 == 15 || i == len-1) fprintf(fp, "\n");
  }
}

void test_crypto(const quic_secret *secret, const unsigned char *expected_cipher)
{
    int result;
    quic_key *key;
    unsigned char cipher[plain_len+16];

    printf("==== test_crypto(%s,%s) ====\n",
        hash_to_name[secret->hash], aead_to_name[secret->ae]);

    result = quic_crypto_derive_key(&key, secret);
    if (result == 0) {
        printf("FAIL: quic_crypto_derive_key failed\n");
        exit(1);
    }

    memset(cipher, 0, sizeof(cipher));
    result = quic_crypto_encrypt(key, cipher, sn, ad, ad_len, plain, plain_len);
    if (result == 0) {
        printf("FAIL: quic_crypto_encrypt failed\n");
        exit(1);
    }

#if 0
    // Capture expected results to files ready to paste into C source code
    char fname[64];
    sprintf(fname, "results_%d_%d", secret->hash, secret->ae);
    FILE *fp = fopen(fname, "w");
    dumptofile(fp, cipher, sizeof(cipher));
    fclose(fp);
#else
    // Verify that the computed text matches expectations
    check_result("quic_crypto_encrypt", cipher, expected_cipher, sizeof(cipher));
#endif

    unsigned char decrypted[plain_len];
    result = quic_crypto_decrypt(key, decrypted, sn, ad, ad_len, cipher, sizeof(cipher));
    if (result == 0) {
        printf("FAIL: quic_crypto_decrypt failed\n");
        exit(1);
    }
    check_result("quic_crypto_decrypt", decrypted, plain, sizeof(decrypted));

    result = quic_crypto_free_key(key);
    if (result == 0) {
        printf("FAIL: quic_crypto_free_key failed\n");
        exit(1);
    }

    printf("PASS\n");
}

const uint8_t expected_client_hs[] =  { // client_hs (draft 19)
0x03,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0xfe,0xf5,0x2b,0x9b,0x3a,0xe4,0x67,0x7a,
0x63,0x67,0xa7,0x74,0x12,0xb1,0x9d,0xdb,0xf1,0x54,0xc9,0xa2,0x55,0xea,0xf8,0x77,
0x18,0x9d,0x96,0x09,0xad,0x5c,0x82,0xab,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
};

const uint8_t expected_server_hs[] = { // server_hs (draft 19)
0x03,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x9a,0x52,0x97,0x7b,0xea,0xd3,0x53,0xc0,
0x8e,0xd7,0x6f,0x54,0x28,0xdb,0x69,0x3f,0xdb,0x74,0x5c,0x0d,0xbe,0xde,0xa2,0x23,
0xf0,0x1f,0x67,0xe5,0xf3,0x4c,0xb6,0xee,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
};

void test_pn_encrypt()
{
  printf("==== test_pn_encrypt() ====\n");

  quic_secret client_hs;
  memset(&client_hs, 0, sizeof(client_hs));

  quic_secret server_hs;
  memset(&server_hs, 0, sizeof(server_hs));

  quic_key *key;
  int result, i;

  /* From Quicly & picoquic test vectors */
  static const uint8_t cid[] = { 0x77, 0x0d, 0xc2, 0x6c, 0x17, 0x50, 0x9b, 0x35 };
  static const uint8_t salt[] = { 0xef, 0x4f, 0xb0, 0xab, 0xb4, 0x74, 0x70, 0xc4, 0x1b, 0xef, 0xcf, 0x80, 0x31, 0x33, 0x4f, 0xae, 0x48, 0x5e, 0x09, 0xa0 };
  static const uint8_t sample[] = { 0x05, 0x80, 0x24, 0xa9, 0x72, 0x75, 0xf0, 0x1d, 0x2a, 0x1e, 0xc9, 0x1f, 0xd1, 0xc2, 0x65, 0xbb };
  static const uint8_t encrypted_pn[] = { 0x70, 0x61, 0x87, 0x5e, 0x08 };
  static const uint8_t expected_pn[] = { 0xc0, 0x00, 0x00, 0x00, 0x00 };
  uint8_t pnmask[5] = {0};

  result = quic_derive_initial_secrets(&client_hs, &server_hs, cid, sizeof(cid), salt, sizeof(salt));
  if (result == 0) {
      printf("FAIL: quic_derive_initial_secrets failed\n");
      exit(1);
  }

  result = quic_crypto_derive_key(&key, &client_hs);
  if (result == 0) {
      printf("FAIL: quic_crypto_derive_key failed\n");
      exit(1);
  }

  if(quic_crypto_hp_mask(key, sample, pnmask))
  {
    printf("PN encryption mask: "); dump(pnmask, 5);
    for(i = 0; i < 5; i++) pnmask[i] ^= encrypted_pn[i];
    printf("Decrypted PN: "); dump(pnmask, 5);
    check_result("decrypted PN", pnmask, expected_pn, sizeof(pnmask));
  } else {
    printf("PN encryption failed.\n");
    exit(1);
  }
}

void test_initial_secrets()
{
    int result;

    printf("==== test_initial_secrets() ====\n");

    quic_secret client_hs;
    memset(&client_hs, 0, sizeof(client_hs));

    quic_secret server_hs;
    memset(&server_hs, 0, sizeof(server_hs));

    const unsigned char con_id[12] = {0xff,0xaa,0x55,0x00, 0x80,0x01,0x7f,0xee, 0x81,0x42,0x24,0x18 };
    const unsigned char salt[] = {0xef, 0x4f, 0xb0, 0xab, 0xb4, 0x74, 0x70, 0xc4, 0x1b, 0xef, 0xcf, 0x80, 0x31, 0x33, 0x4f, 0xae, 0x48, 0x5e, 0x09, 0xa0};
    result = quic_derive_initial_secrets(&client_hs, &server_hs, con_id, sizeof(con_id), salt, sizeof(salt));
    if (result == 0) {
        printf("FAIL: quic_derive_initial_secrets failed\n");
        exit(1);
    }

#if 0
    // Capture expected results to files ready to paste into C source code
    FILE *fp = fopen("client_hs", "w");
    dumptofile(fp, (const uint8_t*)&client_hs, sizeof(client_hs));
    fclose(fp);
    fp = fopen("server_hs", "w");
    dumptofile(fp, (const uint8_t*)&server_hs, sizeof(server_hs));
    fclose(fp);
#else
    // Verify that the computed text matches expectations
    check_result("quic_derive_initial_secrets client", (const unsigned char*)&client_hs, (const unsigned char*)&expected_client_hs, sizeof(client_hs));
    check_result("quic_derive_initial_secrets server", (const unsigned char*)&server_hs, (const unsigned char*)&expected_server_hs, sizeof(server_hs));
#endif

    printf("==== PASS: test_initial_secrets ==== \n");
}

void exhaustive(void)
{
    quic_secret secret;

    for (unsigned char i=0; i<sizeof(secret.secret); ++i) {
        secret.secret[i] = i;
    }

    for (size_t i=0; testcombinations[i].expected_cipher; ++i) {
        secret.hash = testcombinations[i].hash;
        secret.ae = testcombinations[i].ae;

        test_crypto(&secret, testcombinations[i].expected_cipher);
    }

    test_pn_encrypt();
    test_initial_secrets();
}

int CDECL main(int argc, char **argv)
{
    // Reference arguments to avoid compiler errors
    (void)argc;
    (void)argv;

    EverCrypt_AutoConfig2_init();

    coverage();
    exhaustive();

    printf("==== ALL TESTS PASS ====\n");
}
