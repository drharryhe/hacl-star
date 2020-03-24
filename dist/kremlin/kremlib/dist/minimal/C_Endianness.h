/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.

  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: ../krml -fparentheses -fcurly-braces -fno-shadow -header copyright-header.txt -minimal -tmpdir dist/minimal -skip-compilation -extract-uints -add-include <inttypes.h> -add-include <stdbool.h> -add-include "kremlin/internal/compat.h" -add-include "kremlin/lowstar_endianness.h" -add-include "kremlin/internal/types.h" -add-include "kremlin/internal/target.h" -bundle FStar.UInt64+FStar.UInt32+FStar.UInt16+FStar.UInt8=[rename=FStar_UInt_8_16_32_64] -bundle C.Endianness= -library FStar.UInt128 -bundle FStar.UInt128= -bundle *,WindowsWorkaroundSigh fstar_uint128.c -o libkremlib.a .extract/prims.krml .extract/FStar_Pervasives_Native.krml .extract/FStar_Pervasives.krml .extract/FStar_Preorder.krml .extract/FStar_Calc.krml .extract/FStar_Squash.krml .extract/FStar_Classical.krml .extract/FStar_StrongExcludedMiddle.krml .extract/FStar_FunctionalExtensionality.krml .extract/FStar_List_Tot_Base.krml .extract/FStar_List_Tot_Properties.krml .extract/FStar_List_Tot.krml .extract/FStar_Seq_Base.krml .extract/FStar_Seq_Properties.krml .extract/FStar_Seq.krml .extract/FStar_Mul.krml .extract/FStar_Math_Lib.krml .extract/FStar_Math_Lemmas.krml .extract/FStar_BitVector.krml .extract/FStar_UInt.krml .extract/FStar_UInt32.krml .extract/FStar_Int.krml .extract/FStar_Int16.krml .extract/FStar_Reflection_Types.krml .extract/FStar_Reflection_Data.krml .extract/FStar_Order.krml .extract/FStar_Reflection_Basic.krml .extract/FStar_Ghost.krml .extract/FStar_ErasedLogic.krml .extract/FStar_UInt64.krml .extract/FStar_Set.krml .extract/FStar_PropositionalExtensionality.krml .extract/FStar_PredicateExtensionality.krml .extract/FStar_TSet.krml .extract/FStar_Monotonic_Heap.krml .extract/FStar_Heap.krml .extract/FStar_Map.krml .extract/FStar_Monotonic_HyperHeap.krml .extract/FStar_Monotonic_HyperStack.krml .extract/FStar_HyperStack.krml .extract/FStar_Monotonic_Witnessed.krml .extract/FStar_HyperStack_ST.krml .extract/FStar_HyperStack_All.krml .extract/FStar_Date.krml .extract/FStar_Char.krml .extract/FStar_Exn.krml .extract/FStar_ST.krml .extract/FStar_All.krml .extract/FStar_List.krml .extract/FStar_String.krml .extract/FStar_Reflection_Const.krml .extract/FStar_Reflection_Derived.krml .extract/FStar_Reflection_Derived_Lemmas.krml .extract/FStar_Universe.krml .extract/FStar_GSet.krml .extract/FStar_ModifiesGen.krml .extract/FStar_Range.krml .extract/FStar_Tactics_Types.krml .extract/FStar_Tactics_Result.krml .extract/FStar_Tactics_Effect.krml .extract/FStar_Tactics_Builtins.krml .extract/FStar_Reflection.krml .extract/FStar_Tactics_SyntaxHelpers.krml .extract/FStar_Tactics_Util.krml .extract/FStar_Reflection_Formula.krml .extract/FStar_Tactics_Derived.krml .extract/FStar_Tactics_Logic.krml .extract/FStar_Tactics.krml .extract/FStar_BigOps.krml .extract/LowStar_Monotonic_Buffer.krml .extract/LowStar_Buffer.krml .extract/Spec_Loops.krml .extract/LowStar_BufferOps.krml .extract/C_Loops.krml .extract/FStar_UInt8.krml .extract/FStar_Kremlin_Endianness.krml .extract/FStar_UInt63.krml .extract/FStar_Dyn.krml .extract/FStar_Int63.krml .extract/FStar_Int64.krml .extract/FStar_Int32.krml .extract/FStar_Int8.krml .extract/FStar_UInt16.krml .extract/FStar_Int_Cast.krml .extract/FStar_UInt128.krml .extract/C_Endianness.krml .extract/WasmSupport.krml .extract/FStar_Float.krml .extract/FStar_IO.krml .extract/C.krml .extract/LowStar_Modifies.krml .extract/FStar_Bytes.krml .extract/C_String.krml .extract/FStar_HyperStack_IO.krml .extract/LowStar_Printf.krml .extract/C_Failure.krml .extract/TestLib.krml .extract/FStar_Int_Cast_Full.krml
  F* version: bf6726d1
  KreMLin version: 279ad301
*/

#include <inttypes.h>
#include <stdbool.h>
#include "kremlin/internal/compat.h"
#include "kremlin/lowstar_endianness.h"
#include "kremlin/internal/types.h"
#include "kremlin/internal/target.h"

#ifndef __C_Endianness_H
#define __C_Endianness_H

#include "FStar_UInt128.h"


KRML_DEPRECATED("LowStar.Endianness.load128_le")

extern FStar_UInt128_uint128 load128_le(uint8_t *b);

KRML_DEPRECATED("LowStar.Endianness.store128_le")

extern void store128_le(uint8_t *b, FStar_UInt128_uint128 z);

KRML_DEPRECATED("LowStar.Endianness.load128_be")

extern FStar_UInt128_uint128 load128_be(uint8_t *b);

KRML_DEPRECATED("LowStar.Endianness.store128_be")

extern void store128_be(uint8_t *b, FStar_UInt128_uint128 z);

KRML_DEPRECATED("LowStar.Endianness.index_32_be")

uint32_t index_32_be(uint8_t *b, uint32_t i);

KRML_DEPRECATED("LowStar.Endianness.index_32_le")

uint32_t index_32_le(uint8_t *b, uint32_t i);

KRML_DEPRECATED("LowStar.Endianness.index_64_be")

uint64_t index_64_be(uint8_t *b, uint32_t i);

KRML_DEPRECATED("LowStar.Endianness.index_64_le")

uint64_t index_64_le(uint8_t *b, uint32_t i);

KRML_DEPRECATED("LowStar.Endianness.upd_32_be")

void upd_32_be(uint8_t *b, uint32_t i, uint32_t v1);

#define __C_Endianness_H_DEFINED
#endif
