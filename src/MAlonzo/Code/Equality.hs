{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Equality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Reflexive
import qualified MAlonzo.Code.Symmetric
import qualified MAlonzo.Code.Transitive

-- Equality._≡_
d__'8801'__8 a0 a1 a2 a3 = ()
data T__'8801'__8 = C_refl_16
-- Equality._≡ₛ_
d__'8801''8347'__24 a0 a1 a2 a3 = ()
data T__'8801''8347'__24 = C_refl'8347'_32
-- Equality.≡ₛ→≡
d_'8801''8347''8594''8801'_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> AgdaAny -> T__'8801''8347'__24 -> T__'8801'__8
d_'8801''8347''8594''8801'_42 = erased
-- Equality.subst
d_subst_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T__'8801'__8 -> AgdaAny -> AgdaAny
d_subst_56 = erased
-- Equality.substₛ
d_subst'8347'_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T__'8801''8347'__24 -> AgdaAny -> AgdaAny
d_subst'8347'_74 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_subst'8347'_74 v7
du_subst'8347'_74 :: AgdaAny -> AgdaAny
du_subst'8347'_74 v0 = coe v0
-- Equality.substrefl
d_substrefl_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny -> T__'8801''8347'__24 -> AgdaAny -> T__'8801''8347'__24
d_substrefl_94 = erased
-- Equality.happly
d_happly_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T__'8801'__8 -> AgdaAny -> T__'8801'__8
d_happly_124 = erased
-- Equality.happlyₛ
d_happly'8347'_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T__'8801''8347'__24 -> AgdaAny -> T__'8801''8347'__24
d_happly'8347'_144 = erased
-- Equality.funExt
d_funExt_164
  = error
      "MAlonzo Runtime Error: postulate evaluated: Equality.funExt"
-- Equality.funExtₛ
d_funExt'8347'_182
  = error
      "MAlonzo Runtime Error: postulate evaluated: Equality.funExt\8347"
-- Equality.cong
d_cong_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T__'8801'__8 -> T__'8801'__8
d_cong_198 = erased
-- Equality.congₛ
d_cong'8347'_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T__'8801''8347'__24 -> T__'8801''8347'__24
d_cong'8347'_216 = erased
-- Equality._∎
d__'8718'_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> T__'8801'__8
d__'8718'_226 = erased
-- Equality._∎ₛ
d__'8718''8347'_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> T__'8801''8347'__24
d__'8718''8347'_236 = erased
-- Equality.≡ₛTrans
d_'8801''8347'Trans_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> MAlonzo.Code.Transitive.T_Transitive_8
d_'8801''8347'Trans_244 ~v0 ~v1 = du_'8801''8347'Trans_244
du_'8801''8347'Trans_244 :: MAlonzo.Code.Transitive.T_Transitive_8
du_'8801''8347'Trans_244
  = coe MAlonzo.Code.Transitive.C_Transitive'46'constructor_19 erased
-- Equality.≡Trans
d_'8801'Trans_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> MAlonzo.Code.Transitive.T_Transitive'8346'_58
d_'8801'Trans_252 = erased
-- Equality._≡⟨_⟩_
d__'8801''10216'_'10217'__266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T__'8801'__8 -> T__'8801'__8 -> T__'8801'__8
d__'8801''10216'_'10217'__266 = erased
-- Equality._≡⟨_⟩ₛ_
d__'8801''10216'_'10217''8347'__284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__'8801''8347'__24 -> T__'8801''8347'__24 -> T__'8801''8347'__24
d__'8801''10216'_'10217''8347'__284 = erased
-- Equality.≡ₛRefl
d_'8801''8347'Refl_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> MAlonzo.Code.Reflexive.T_Reflexive_8
d_'8801''8347'Refl_296 ~v0 ~v1 = du_'8801''8347'Refl_296
du_'8801''8347'Refl_296 :: MAlonzo.Code.Reflexive.T_Reflexive_8
du_'8801''8347'Refl_296
  = coe MAlonzo.Code.Reflexive.C_Reflexive'46'constructor_7 erased
-- Equality.≡Refl
d_'8801'Refl_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> MAlonzo.Code.Reflexive.T_Reflexive'8346'_34
d_'8801'Refl_302 = erased
-- Equality.≡ₛSym
d_'8801''8347'Sym_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> MAlonzo.Code.Symmetric.T_Symmetric_8
d_'8801''8347'Sym_308 ~v0 ~v1 = du_'8801''8347'Sym_308
du_'8801''8347'Sym_308 :: MAlonzo.Code.Symmetric.T_Symmetric_8
du_'8801''8347'Sym_308
  = coe MAlonzo.Code.Symmetric.C_Symmetric'46'constructor_13 erased
-- Equality.≡Sym
d_'8801'Sym_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> MAlonzo.Code.Symmetric.T_Symmetric'8346'_38
d_'8801'Sym_316 = erased
