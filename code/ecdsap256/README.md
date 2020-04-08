# The purpose of the branch

1) provide a unique (and hopefully the only) buffer for the data we suppose to be secret. After the operations the buffer is cleaned. NB: some compilers could NOT to preserve this property

2) Comparing the buffers at the input


# Non-constant-time functions in this folder

## These functions are not side-channel resistant

Hacl.Impl.P256.Signature.Common.eq_u64_nCT
Hacl.Impl.P256.Signature.Common.eq_0_u64
Hacl.Impl.P256.Signature.Common.isCoordinateValid
Hacl.Impl.P256.Signature.Common.verifyQValidCurvePoint
Hacl.Impl.P256.Signature.Common.isPointAtInfinityPublic
Hacl.Impl.P256.Signature.Common.isPointOnCurvePublic
Hacl.Impl.P256.Signature.Common.isOrderCorrect

Hacl.Impl.ECDSA.P256SHA256.Verification.isZero_uint64_nCT
Hacl.Impl.ECDSA.P256SHA256.Verification.isMoreThanZeroLessThanOrderMinusOne
Hacl.Impl.ECDSA.P256SHA256.Verification.compare_felem_bool
Hacl.Impl.ECDSA.P256SHA256.Verification.ecdsa_verification_step1
Hacl.Impl.ECDSA.P256SHA256.Verification.ecdsa_verification_step5
Hacl.Impl.ECDSA.P256SHA256.Verification.ecdsa_verification

Hacl.Impl.ECDSA.ecdsa_p256_sha2_verify
Hacl.Impl.ECDSA.ecdsa_p256_sha2_verify_u8

## These functions are constant-time on `scalar` but not on `pubKey`

Hacl.Impl.P256.DH._ecp256dh_r result pubKey scalar
Hacl.Impl.P256.DH.ecp256dh_r result pubKey scalar

