/* SPDX-License-Identifier: BSD-2-Clause */

/* Keep checks enabled when inherited compiler flags define NDEBUG. */
#undef NDEBUG
#include <assert.h>
#include <string.h>

#include "rts.h"

/* The runtime normally obtains these definitions from the generated model. */
#ifdef __cplusplus
extern "C" {
#endif
void (*sail_rts_set_coverage_file)(const char *) = NULL;
void model_pre_exit(void) {}
extern struct block *sail_memory;
#ifdef __cplusplus
}
#endif

static const uint64_t block_size = UINT64_C(1) << 24;

static void test_empty_and_missing(void)
{
  uint8_t data[32];
  read_mem_bytes(UINT64_MAX, NULL, 0);
  write_mem_bytes(UINT64_MAX, NULL, 0);
  assert(sail_memory == NULL);

  memset(data, 0xff, sizeof(data));
  read_mem_bytes(block_size - 7, data, sizeof(data));
  for (size_t i = 0; i < sizeof(data); ++i) {
    assert(data[i] == 0);
  }
  assert(sail_memory == NULL);
}

/* Compare bulk transfers with the existing byte interface, including guards. */
static void test_transfer(uint64_t address, size_t length)
{
  uint8_t expected[4097];
  uint8_t actual[sizeof(expected) + 2];
  assert(length <= sizeof(expected));
  for (size_t i = 0; i < length; ++i) {
    expected[i] = (uint8_t)(37 * i + 131);
  }

  write_mem(address - 1, 0x12);
  write_mem(address + length, 0x34);
  write_mem_bytes(address, expected, length);
  assert(read_mem(address - 1) == 0x12);
  assert(read_mem(address + length) == 0x34);
  for (size_t i = 0; i < length; ++i) {
    assert(read_mem(address + i) == expected[i]);
    expected[i] ^= 0xff;
    write_mem(address + i, expected[i]);
  }

  memset(actual, 0xa5, sizeof(actual));
  read_mem_bytes(address, actual + 1, length);
  assert(actual[0] == 0xa5);
  assert(actual[length + 1] == 0xa5);
  assert(memcmp(actual + 1, expected, length) == 0);
}

/* A single transfer must traverse an entire absent block between present ones. */
static void test_sparse_transfers(void)
{
  size_t length = (size_t)block_size + 32;
  uint64_t address = 3 * block_size - 16;
  uint8_t *data = (uint8_t *)malloc(length);
  assert(data != NULL);
  write_mem(address, 0x56);
  write_mem(address + length - 1, 0x78);
  memset(data, 0xff, length);
  struct block *before = sail_memory;
  read_mem_bytes(address, data, length);
  assert(sail_memory == before);
  assert(data[0] == 0x56);
  assert(data[length - 1] == 0x78);
  for (size_t i = 1; i < length - 1; ++i) {
    assert(data[i] == 0);
  }
  /* Reuse the hole to exercise a write spanning three consecutive blocks. */
  memset(data, 0x9a, length);
  write_mem_bytes(address, data, length);
  for (size_t i = 0; i < length; ++i) {
    assert(read_mem(address + i) == data[i]);
  }
  free(data);
}

static void test_tags(void)
{
  uint64_t address = 7 * block_size - 4;
  uint8_t bytes[8] = {0};
  write_tag_bool(address, true);
  write_tag_bool(address + 7, true);
  write_mem_bytes(address, bytes, sizeof(bytes));
  read_mem_bytes(address, bytes, sizeof(bytes));
  assert(read_tag_bool(address));
  assert(read_tag_bool(address + 7));
  assert(!read_tag_bool(address + 1));
}

/* Reproduce the original little-endian byte-loop oracle for both RAM readers. */
static void test_ram_readers(uint64_t address)
{
  uint8_t bytes[65];
  mpz_t addr_size, data_size, addr, value, expected;
  mpz_inits(addr_size, data_size, addr, value, expected, NULL);
  mpz_set_ui(addr_size, 64);
  mpz_set_ui(addr, address);
  lbits address_bv = {64, &addr};
  lbits data = {0, &value};
  lbits unused = {0, NULL};

  for (size_t i = 0; i < sizeof(bytes); ++i) {
    bytes[i] = (uint8_t)(17 * i + 129);
  }
  /* Non-canonical leading zero bytes must still contribute to the width. */
  bytes[7] = bytes[8] = bytes[15] = bytes[64] = 0;
  write_mem_bytes(address, bytes, sizeof(bytes));

  const size_t widths[] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 16, 65};
  for (size_t w = 0; w < sizeof(widths) / sizeof(widths[0]); ++w) {
    size_t length = widths[w];
    mpz_set_ui(expected, 0);
    for (size_t i = length; i > 0; --i) {
      mpz_mul_2exp(expected, expected, 8);
      mpz_add_ui(expected, expected, read_mem(address + i - 1));
    }
    mpz_set_ui(data_size, length);
    /* A zero or short read must replace, rather than retain, the old value. */
    mpz_set_si(value, -1);
    read_ram(&data, addr_size, data_size, unused, address_bv);
    assert(data.len == length * 8);
    assert(mpz_cmp(value, expected) == 0);
    uint64_t small_expected = 0;
    for (size_t i = length; i > 0; --i) {
      small_expected = (small_expected << 8) | read_mem(address + i - 1);
    }
    sbits small = fast_read_ram((int64_t)length, address);
    assert(small.len == length * 8);
    assert(small.bits == small_expected);
  }
  mpz_clears(addr_size, data_size, addr, value, expected, NULL);
}

static void test_raw_loader(void)
{
  const char *filename = "image.bin";
  uint64_t address = 9 * block_size - 100;
  uint8_t expected[4096 + 37], actual[sizeof(expected)];
  for (size_t i = 0; i < sizeof(expected); ++i) {
    expected[i] = (uint8_t)(19 * i + 251);
  }
  FILE *file = fopen(filename, "wb");
  assert(file != NULL);
  assert(fwrite(expected, 1, sizeof(expected), file) == sizeof(expected));
  assert(fclose(file) == 0);

  write_mem(address - 1, 0x12);
  write_mem(address + sizeof(expected), 0x34);
  load_raw(address, filename);
  read_mem_bytes(address, actual, sizeof(actual));
  assert(memcmp(actual, expected, sizeof(actual)) == 0);
  assert(read_mem(address - 1) == 0x12);
  assert(read_mem(address + sizeof(expected)) == 0x34);

  file = fopen(filename, "wb");
  assert(file != NULL);
  assert(fclose(file) == 0);
  struct block *before = sail_memory;
  load_raw(11 * block_size, filename);
  assert(sail_memory == before);
  assert(remove(filename) == 0);
}

int main(void)
{
  setup_rts();
  test_empty_and_missing();

  const uint64_t addresses[] = {3, block_size - 7, UINT64_MAX - 3};
  const size_t lengths[] = {0, 1, 7, 8, 9, 257, 4097};
  for (size_t a = 0; a < sizeof(addresses) / sizeof(addresses[0]); ++a) {
    for (size_t n = 0; n < sizeof(lengths) / sizeof(lengths[0]); ++n) {
      test_transfer(addresses[a], lengths[n]);
    }
    test_ram_readers(addresses[a]);
  }
  test_sparse_transfers();
  test_tags();
  test_raw_loader();
  cleanup_rts();

  /* Cleanup must clear all blocks and leave the runtime reusable. */
  setup_rts();
  test_empty_and_missing();
  test_transfer(block_size - 1, 9);
  assert(!read_tag_bool(7 * block_size - 4));
  cleanup_rts();
  return 0;
}
