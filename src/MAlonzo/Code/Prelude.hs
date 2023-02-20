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

module MAlonzo.Code.Prelude where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Prelude.the
d_the_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny -> AgdaAny
d_the_6 ~v0 ~v1 v2 = du_the_6 v2
du_the_6 :: AgdaAny -> AgdaAny
du_the_6 v0 = coe v0
-- Prelude.typeOf
d_typeOf_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny -> ()
d_typeOf_14 = erased
-- Prelude.id
d_id_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny -> AgdaAny
d_id_22 ~v0 ~v1 v2 = du_id_22 v2
du_id_22 :: AgdaAny -> AgdaAny
du_id_22 v0 = coe v0
-- Prelude.idP
d_idP_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny -> AgdaAny
d_idP_30 = erased
-- Prelude._∘_
d__'8728'__52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'8728'__52 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du__'8728'__52 v6 v7 v8
du__'8728'__52 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'8728'__52 v0 v1 v2 = coe v0 (coe v1 v2)
-- Prelude._∘P_
d__'8728'P__78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'8728'P__78 = erased
-- Prelude._⊚_
d__'8858'__112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'8858'__112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du__'8858'__112 v6 v7 v8
du__'8858'__112 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'8858'__112 v0 v1 v2 = coe v0 v2 (coe v1 v2)
-- Prelude.flip
d_flip_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_flip_132 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 = du_flip_132 v6 v7 v8
du_flip_132 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_flip_132 v0 v1 v2 = coe v0 v2 v1
-- Prelude.const
d_const_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_const_148 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_const_148 v4
du_const_148 :: AgdaAny -> AgdaAny
du_const_148 v0 = coe v0
-- Prelude.Σ
d_Σ_162 a0 a1 a2 a3 = ()
data T_Σ_162 = C__'44'Σ__180 AgdaAny AgdaAny
-- Prelude.Σ.π₁
d_π'8321'_176 :: T_Σ_162 -> AgdaAny
d_π'8321'_176 v0
  = case coe v0 of
      C__'44'Σ__180 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Prelude.Σ.π₂
d_π'8322'_178 :: T_Σ_162 -> AgdaAny
d_π'8322'_178 v0
  = case coe v0 of
      C__'44'Σ__180 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Prelude._×_
d__'215'__186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> () -> ()
d__'215'__186 = erased
-- Prelude._,_
d__'44'__202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> AgdaAny -> AgdaAny -> T_Σ_162
d__'44'__202 ~v0 ~v1 ~v2 ~v3 v4 v5 = du__'44'__202 v4 v5
du__'44'__202 :: AgdaAny -> AgdaAny -> T_Σ_162
du__'44'__202 v0 v1 = coe C__'44'Σ__180 (coe v0) (coe v1)
-- Prelude._↔_
d__'8596'__216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> () -> ()
d__'8596'__216 = erased
-- Prelude.⊥
d_'8869'_222 = ()
data T_'8869'_222
-- Prelude.⊥ₚ
d_'8869''8346'_224 = ()
data T_'8869''8346'_224
-- Prelude.exfalso
d_exfalso_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> T_'8869'_222 -> AgdaAny
d_exfalso_230 ~v0 ~v1 ~v2 = du_exfalso_230
du_exfalso_230 :: AgdaAny
du_exfalso_230 = MAlonzo.RTE.mazUnreachableError
-- Prelude.exfalsoₚ
d_exfalso'8346'_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> T_'8869''8346'_224 -> AgdaAny
d_exfalso'8346'_236 ~v0 ~v1 ~v2 = du_exfalso'8346'_236
du_exfalso'8346'_236 :: AgdaAny
du_exfalso'8346'_236 = MAlonzo.RTE.mazUnreachableError
-- Prelude.exfalsoₚₚ
d_exfalso'8346''8346'_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> T_'8869''8346'_224 -> AgdaAny
d_exfalso'8346''8346'_242 ~v0 ~v1 ~v2 = du_exfalso'8346''8346'_242
du_exfalso'8346''8346'_242 :: AgdaAny
du_exfalso'8346''8346'_242 = MAlonzo.RTE.mazUnreachableError
-- Prelude.⊤
d_'8868'_244 = ()
data T_'8868'_244 = C_trivial_246
-- Prelude.¬_
d_'172'__252 :: MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_'172'__252 = erased
-- Prelude.¬ₚ_
d_'172''8346'__260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_'172''8346'__260 = erased
-- Prelude.weaken
d_weaken_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> (AgdaAny -> T_'8869'_222) -> T_'8869'_222
d_weaken_268 = erased
-- Prelude.Endo
d_Endo_278 a0 a1 = ()
newtype T_Endo_278 = C_mkEndo_288 (AgdaAny -> AgdaAny)
-- Prelude.Endo.endo
d_endo_286 :: T_Endo_278 -> AgdaAny -> AgdaAny
d_endo_286 v0
  = case coe v0 of
      C_mkEndo_288 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Prelude.Dual
d_Dual_294 a0 a1 = ()
newtype T_Dual_294 = C_mkDual_304 AgdaAny
-- Prelude.Dual.dual
d_dual_302 :: T_Dual_294 -> AgdaAny
d_dual_302 v0
  = case coe v0 of
      C_mkDual_304 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
