module Hacl.Impl.ECDSA.Defensive

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.ECDSAP256.Definition

open Spec.Hash.Definitions


assume val ecdsa_signature: alg: hash_alg {SHA2_256? alg \/ SHA2_384? alg \/ SHA2_512? alg} -> result: lbuffer uint8 (size 64) -> mLen: size_t -> m: lbuffer uint8 mLen ->
  privKey: lbuffer uint8 (size 32) -> 
  k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) < prime_p256_order /\
    nat_from_bytes_be (as_seq h k) < prime_p256_order
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature_agile alg (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec 
    )    
  )


val returnRandom: unit -> Tot uint64

let returnRandom () = 
  (* for now random is this value *)
  (u64 15624032632068572989)


val cleanUpCritical: critical : lbuffer uint64 (size 4) -> Stack unit
  (requires fun h -> live h critical)
  (ensures fun h0 _ h1 -> modifies (loc critical) h0 h1)

let cleanUpCritical critical = 
  upd critical (size 0) (returnRandom ());
  upd critical (size 1) (returnRandom ());
  upd critical (size 2) (returnRandom ());
  upd critical (size 3) (returnRandom())


val lessThanOrderU8: i: lbuffer uint8 (size 32) -> critical: lbuffer uint64 (size 4) -> Stack uint64 
  (requires fun h -> live h i /\ disjoint i critical)
  (ensures fun h0 r h1 -> modifies (loc critical) h0 h1 /\ uint_v r == 0 ==> nat_from_bytes_be (as_seq h0 i) < prime_p256_order)

let lessThanOrderU8 i critical = 
  admit();
  cleanUpCritical critical;
  (u64 0)


assume val compareTo0TwoVariablesNotSC: a: uint64 -> b: uint64 ->
  Tot (r : bool {r = (uint_v a = 0 && uint_v b = 0)})


val ecdsa_signature_defensive: alg: hash_alg -> result: lbuffer uint8 (size 64) -> mLen: size_t -> m: lbuffer uint8 mLen ->
  privKey: lbuffer uint8 (size 32) -> 
  k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k /\
    nat_from_bytes_be (as_seq h privKey) < prime_p256_order /\
    nat_from_bytes_be (as_seq h k) < prime_p256_order
  )
  (ensures fun h0 flag h1 -> True (*
    modifies (loc result) h0 h1
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature_agile alg (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec  *)

    )


#set-options "--z3rlimit 300"


let ecdsa_signature_defensive alg result mLen m privKey k = 
  (*SHA2_256? alg \/ SHA2_384? alg \/ SHA2_512? alg *)
  push_frame();  
  if alg = SHA2_256 || alg = SHA2_384 || alg = SHA2_512  
    then 
      begin
	let cr0 = create (size 4) (u64 0) in 
	let cr1 = create (size 4) (u64 0) in  
	let less0 = lessThanOrderU8 privKey cr0 in 
	let less1 = lessThanOrderU8 k cr0 in 
      (* having if here to leak only if the private data is less than order or not *)
	let flagLessOrder = compareTo0TwoVariablesNotSC less0 less1 in 
	  if flagLessOrder then 
	    begin
	      let h1 = ST.get() in 
	      assume (nat_from_bytes_be (as_seq h1 privKey) < prime_p256_order); 
	      assume (nat_from_bytes_be (as_seq h1 k) < prime_p256_order); 
	      let r = ecdsa_signature alg result mLen m privKey k in 
	      pop_frame();
	      r
	    end
	  else
	    begin 
	      pop_frame();
	      u64 (maxint U64)
	    end 
    end
  else begin
    pop_frame();
    u64 (maxint U64)
    end
