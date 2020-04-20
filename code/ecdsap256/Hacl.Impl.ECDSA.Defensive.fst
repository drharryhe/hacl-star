module Hacl.Impl.ECDSA.Defensive

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.ECDSAP256.Definition

open Spec.Hash.Definitions
open Lib.Memzero2
open Hacl.Impl.LowLevel

open Spec.P256.Lemmas
open Hacl.Impl.ECDSA.MontgomeryMultiplication


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

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"


val cleanUpCritical: critical : lbuffer uint64 (size 4) -> Stack unit
  (requires fun h -> live h critical)
  (ensures fun h0 _ h1 -> modifies (loc critical) h0 h1 /\ as_seq h1 critical == Seq.create 4 (u64 0))

let cleanUpCritical critical = 
  mem_zero_u64 (size 4) critical


open Lib.IntTypes.Intrinsics
open FStar.Mul

val sub4: x: felem ->  result: felem -> 
  Stack uint64
    (requires fun h -> live h x /\ live h result /\ disjoint x result)
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ (if (nat_from_intseq_be (as_seq h0 x) >= prime_p256_order) then uint_v c = 0 else uint_v c = 1))

let sub4 x result = 
  let h0 = ST.get() in 
    let r0 = sub result (size 0) (size 1) in 
    let r1 = sub result (size 1) (size 1) in 
    let r2 = sub result (size 2) (size 1) in 
    let r3 = sub result (size 3) (size 1) in 

    recall_contents prime256order_buffer (Lib.Sequence.of_list p256_order_prime_list);

    let cc0 = sub_borrow_u64 (u64 0) x.(size 3) prime256order_buffer.(size 0) r0 in 
      let h1 = ST.get() in 
    let cc1 = sub_borrow_u64 cc0 x.(size 2) prime256order_buffer.(size 1) r1 in 
      let h2 = ST.get() in 
    let cc2 = sub_borrow_u64 cc1 x.(size 1) prime256order_buffer.(size 2) r2 in 
      let h3 = ST.get() in 
    let cc3 = sub_borrow_u64 cc2 x.(size 0) prime256order_buffer.(size 3) r3 in 
      let h4 = ST.get() in 

    let open Lib.Sequence in 

    nat_from_intseq_be_slice_lemma (as_seq h0 x) 3;
    nat_from_intseq_be_lemma0 (slice (as_seq h0 x) 3 4);
    
    assert(nat_from_intseq_be (as_seq h0 x) == 
      v (index (as_seq h0 x) 3)  + 
      pow2 64 * nat_from_intseq_be (slice (as_seq h0 x) 0 3));

    assert(disjoint prime256order_buffer result);


	 assert(
	     uint_v (index (as_seq h4 r3) 0) * pow2 64 * pow2 64 * pow2 64 
	   + uint_v (index (as_seq h4 r2) 0) * pow2 64 * pow2 64
	   + uint_v (index (as_seq h4 r1) 0) * pow2 64 
	   + uint_v (index (as_seq h4 r0) 0) 
	   
	   - v cc3 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = 
	   
	     v (index (as_seq h0 x) 0) * pow2 64 * pow2 64 * pow2 64 
	   + v (index (as_seq h0 x) 1) * pow2 64 * pow2 64 
	   + v (index (as_seq h0 x) 2) * pow2 64 
	   + v (index (as_seq h0 x) 3) 

- prime_p256_order);  





    admit();

      assert_norm (pow2 64 * pow2 64 = pow2 128);
      assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
      assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    admit();
    cc3
    


val lessThanOrderU8: i: lbuffer uint8 (size 32) -> critical: lbuffer uint64 (size 4) -> critical1: lbuffer uint64 (size 4) -> Stack uint64 
  (requires fun h -> live h i /\ live h critical /\ live h critical1 /\ disjoint i critical /\ disjoint critical critical1)
  (ensures fun h0 r h1 -> modifies (loc critical |+| loc critical1) h0 h1 /\  uint_v r == 0 ==> nat_from_bytes_be (as_seq h0 i) < prime_p256_order)

let lessThanOrderU8 i critical critical1 = 
    let h0 = ST.get() in 
  toUint64 i critical;
    let h1 = ST.get() in 
    Lib.ByteSequence.uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h0 i);
    
  let carry = sub4 critical  critical1 in 
  let less = eq_mask carry (u64 0) in 
  eq_mask_lemma carry (u64 0);
  cleanUpCritical critical;
  cleanUpCritical critical1;
  less


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
