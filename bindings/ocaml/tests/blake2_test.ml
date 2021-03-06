#include "config.h"

open Test_utils
open AutoConfig2

type 'a blake2_test =
  { name: string; plaintext: 'a; key: 'a; expected: 'a }

let blake2b_tests = [
  {
    name = "Test 1";
    plaintext = Bytes.of_string "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f\x20\x21\x22\x23\x24\x25\x26\x27\x28\x29\x2a\x2b";
    key = Bytes.of_string "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f\x20\x21\x22\x23\x24\x25\x26\x27\x28\x29\x2a\x2b\x2c\x2d\x2e\x2f\x30\x31\x32\x33\x34\x35\x36\x37\x38\x39\x3a\x3b\x3c\x3d\x3e\x3f";
    expected = Bytes.of_string "\xc8\xf6\x8e\x69\x6e\xd2\x82\x42\xbf\x99\x7f\x5b\x3b\x34\x95\x95\x08\xe4\x2d\x61\x38\x10\xf1\xe2\xa4\x35\xc9\x6e\xd2\xff\x56\x0c\x70\x22\xf3\x61\xa9\x23\x4b\x98\x37\xfe\xee\x90\xbf\x47\x92\x2e\xe0\xfd\x5f\x8d\xdf\x82\x37\x18\xd8\x6d\x1e\x16\xc6\x09\x00\x71"
  }
]

let blake2s_tests = [
  {
    name = "Test 1";
    plaintext = Bytes.of_string "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f\x20\x21\x22\x23\x24\x25\x26\x27\x28\x29\x2a\x2b\x2c\x2d\x2e\x2f\x30\x31\x32\x33\x34\x35\x36\x37\x38\x39\x3a\x3b\x3c\x3d\x3e";
    key = Bytes.of_string "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f";
    expected = Bytes.of_string "\xc6\x53\x82\x51\x3f\x07\x46\x0d\xa3\x98\x33\xcb\x66\x6c\x5e\xd8\x2e\x61\xb9\xe9\x98\xf4\xb0\xc4\x28\x7c\xee\x56\xc3\xcc\x9b\xcd"
  }
]

let test (v: Bytes.t blake2_test) n hash reqs =
  let test_result = test_result (n ^ " " ^ v.name) in

  if supports reqs then begin
    let output = Test_utils.init_bytes (Bytes.length v.expected) in

    hash v.key v.plaintext output;
    if Bytes.compare output v.expected = 0 then
      test_result Success ""
    else
      test_result Failure "Output mismatch"
  end else
    test_result Skipped "Required CPU feature not detected"

let _ =
  List.iter (fun v -> test v "Blake2b_32" Hacl.Blake2b_32.hash []) blake2b_tests;
  List.iter (fun v -> test v "Blake2s_32" Hacl.Blake2s_32.hash []) blake2s_tests;

  #if not (defined IS_NOT_X64) || defined IS_ARM_8
  List.iter (fun v -> test v "Blake2s_128" Hacl.Blake2s_128.hash [AVX]) blake2s_tests;
  #endif

  #ifndef IS_NOT_X64
  List.iter (fun v -> test v "Blake2b_256" Hacl.Blake2b_256.hash [AVX2]) blake2b_tests
  #endif

