module Hacl.Impl.P256.Compression

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256
open Hacl.Impl.LowLevel
open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P256.MM.Exponent
open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Impl.P256.Arithmetics

open Hacl.Impl.LowLevel.RawCmp

open Spec.P256.MontgomeryMultiplication

open Spec.P256.Definitions

open FStar.Math.Lemmas

open FStar.Mul

#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"

val uploadA: a: felem -> Stack unit
  (requires fun h -> live h a)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1 /\ 
    as_nat h1 a == toDomain_ (Spec.P256.aCoordinateP256 % prime256) /\
    as_nat h1 a < prime256
 )

let uploadA a = 
  lemmaToDomain (Spec.P256.aCoordinateP256 % prime256);
  upd a (size 0) (u64 18446744073709551612);
  upd a (size 1) (u64 17179869183);
  upd a (size 2) (u64 0);
  upd a (size 3) (u64 18446744056529682436);
  assert_norm(18446744073709551612 + 17179869183 * pow2 64 + 18446744056529682436 * pow2 64 * pow2 64 * pow2 64 = (Spec.P256.aCoordinateP256 % prime256) * pow2 256 % prime256)

val uploadB: b: felem -> Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_nat h1 b < prime256 /\ 
    as_nat h1 b == toDomain_ (Spec.P256.bCoordinateP256))

let uploadB b = 
  lemmaToDomain (Spec.P256.bCoordinateP256);
  upd b (size 0) (u64 15608596021259845087);
  upd b (size 1) (u64 12461466548982526096);
  upd b (size 2) (u64 16546823903870267094);
  upd b (size 3) (u64 15866188208926050356);
  assert_norm (15608596021259845087 + 12461466548982526096 * pow2 64 + 16546823903870267094 * pow2 64 * pow2 64 + 15866188208926050356 * pow2 64 * pow2 64 * pow2 64 == (Spec.P256.bCoordinateP256 * pow2 256 % prime256))


val computeYFromX: x: felem ->  result: felem -> sign: uint64 -> Stack unit 
  (requires fun h -> live h x /\ live h result /\ as_nat h x < prime256 /\ disjoint x result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 result < prime256 /\
    (
      let xD = fromDomain_ (as_nat h0 x) in 
      if uint_v sign = 0 then 
	as_nat h1 result = toDomain_ ((0 - sq_root_spec ((xD * xD * xD + Spec.P256.aCoordinateP256 * xD + Spec.P256.bCoordinateP256) % prime256)) % prime256) else
	as_nat h1 result = toDomain_ (sq_root_spec ((xD * xD * xD + Spec.P256.aCoordinateP256 * xD + Spec.P256.bCoordinateP256) % prime256)))
  )

let computeYFromX x result sign = 
  push_frame();
    let aCoordinateBuffer = create (size 4) (u64 0) in 
    let bCoordinateBuffer = create (size 4) (u64 0) in 

  let h0 = ST.get() in 
    uploadA aCoordinateBuffer;
    uploadB bCoordinateBuffer;
    montgomery_multiplication_buffer aCoordinateBuffer x aCoordinateBuffer;
    cube x result;
    p256_add result aCoordinateBuffer result;
    p256_add result bCoordinateBuffer result;
    uploadZeroImpl aCoordinateBuffer; 

  let h6 = ST.get() in 
    lemmaFromDomain (as_nat h6 aCoordinateBuffer);
    assert_norm (0 * Spec.P256.Lemmas.modp_inv2 (pow2 256) % prime256 == 0);
    square_root result result;
    
    p256_sub aCoordinateBuffer result bCoordinateBuffer;
    
    cmovznz4 sign bCoordinateBuffer result result;

  let h9 = ST.get() in 
    assert(modifies (loc aCoordinateBuffer |+| loc bCoordinateBuffer |+| loc result) h0 h9);
    lemmaFromDomainToDomain (as_nat h9 result);
    pop_frame();

  let x_ = fromDomain_ (as_nat h0 x) in

  calc (==) {
    toDomain_ ((((x_ * x_ * x_ % prime256 + ((Spec.P256.aCoordinateP256 % prime256) * x_ % prime256)) % prime256) + Spec.P256.bCoordinateP256) % prime256);
    (==) {lemma_mod_add_distr Spec.P256.bCoordinateP256 (x_ * x_ * x_ % prime256 + ((Spec.P256.aCoordinateP256 % prime256) * x_ % prime256)) prime256}
    toDomain_ ((x_ * x_ * x_ % prime256 + (Spec.P256.aCoordinateP256 % prime256) * x_ % prime256 + Spec.P256.bCoordinateP256) % prime256);
    (==) {lemma_mod_add_distr ((Spec.P256.aCoordinateP256 % prime256) * x_ % prime256 + Spec.P256.bCoordinateP256) (x_ * x_ * x_) prime256}
    toDomain_ ((x_ * x_ * x_ + (Spec.P256.aCoordinateP256 % prime256) * x_ % prime256 + Spec.P256.bCoordinateP256) % prime256); 
    (==) {lemma_mod_mul_distr_l Spec.P256.aCoordinateP256 x_ prime256}
    toDomain_ ((x_ * x_ * x_ + Spec.P256.aCoordinateP256 * x_ % prime256 + Spec.P256.bCoordinateP256) % prime256); 
    (==) {lemma_mod_add_distr (x_ * x_ * x_ + Spec.P256.bCoordinateP256) (Spec.P256.aCoordinateP256 * x_) prime256}
    toDomain_ ((x_ * x_ * x_ + Spec.P256.aCoordinateP256 * x_ + Spec.P256.bCoordinateP256) % prime256); };

  lemma_mod_sub_distr 0 (x_ * x_ * x_ + Spec.P256.aCoordinateP256 * x_ + Spec.P256.bCoordinateP256) prime256


let decompressionNotCompressedForm b result = 
  let h0 = ST.get() in 
  let compressionIdentifier = index b (size 0) in
  let correctIdentifier = eq_u8_nCT (u8 4) compressionIdentifier in 
  if correctIdentifier then 
    copy result (sub b (size 1) (size 64));
  correctIdentifier


val lessThanPrime: f: felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r = (as_nat h0 f < prime256))

let lessThanPrime f = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
    let carry = sub4_il f prime256_buffer tempBuffer in 
    let less = eq_u64_nCT carry (u64 1) in 
  pop_frame();
    less



let decompressionCompressedForm b result = 
  push_frame();
    let h0 = ST.get() in 
    let temp = create (size 4) (u64 0) in 
    let temp2 = create (size 4) (u64 0) in 

    let open Lib.RawIntTypes in 

    let compressedIdentifier = index b (size 0) in 
    let correctIdentifier2 = eq_mask (u8 2) compressedIdentifier in 
      eq_mask_lemma (u8 2) compressedIdentifier;
    let correctIdentifier3 = eq_mask (u8 3) compressedIdentifier in 
      eq_mask_lemma (u8 3) compressedIdentifier;
    let isIdentifierCorrect =  logor correctIdentifier2 correctIdentifier3 in 
      logor_lemma correctIdentifier2 correctIdentifier3;

    if u8_to_UInt8 isIdentifierCorrect = 255uy then 
    begin
      let x = sub b (size 1) (size 32) in 
      copy (sub result (size 0) (size 32)) x;
(*till here I am BIG-ENDIAN *)
      toUint64ChangeEndian x temp;

	let h1 = ST.get() in 

      Spec.P256.Lemmas.lemma_core_0 temp h1;
      
      let lessThanPrimeXCoordinate = lessThanPrime temp in 
	Spec.ECDSA.changeEndianLemma (Lib.ByteSequence.uints_from_bytes_be (as_seq h0 x));
	Lib.ByteSequence.uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h0 x);

      if not (lessThanPrimeXCoordinate) then 
	begin
	  pop_frame();
	  false
	end  
      else 
	begin
	  toDomain temp temp;
	  lemmaToDomain (as_nat h1 temp);
	  computeYFromX temp temp2 (to_u64 correctIdentifier2);
	  fromDomain temp2 temp2;
	    let h4 = ST.get() in 

	  changeEndian temp2;
	  toUint8 temp2 (sub result (size 32) (size 32));

	  Spec.P256.Lemmas.lemma_core_0 temp2 h4;
	  
	  Lib.ByteSequence.lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h4 temp2);
	  Spec.ECDSA.changeEndian_le_be (as_nat h4 temp2);
	
	  pop_frame();
	  true
	end
    end
  else 
    begin
      pop_frame();
      false
    end
 

let compressionNotCompressedForm b result = 
  upd result (size 0) (u8 4);
  admit();
  copy (sub result (size 1) (size 64)) b
 

let compressionCompressedForm b result = 
  let lastWordY = index b (size 63) in 
  let lastBitY = logand lastWordY (u8 1) in 
    logand_le lastWordY (u8 1);
  let identifier = add lastBitY (u8 2) in 
  upd result (size 0) identifier;
  copy (sub result (size 1) (size 32)) (sub b (size 0) (size 32)) 
