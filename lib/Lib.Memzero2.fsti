module Lib.Memzero2

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer


noextract
val mem_zero_u64: l: size_t -> b: lbuffer uint64 l -> 
  Stack unit 
    (requires fun h -> live h b)
    (ensures fun h0 _ h1 -> True)
    
