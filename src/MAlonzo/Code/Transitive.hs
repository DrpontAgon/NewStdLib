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

module MAlonzo.Code.Transitive where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Transitive.Transitive
d_Transitive_8 a0 a1 a2 = ()
newtype T_Transitive_8
  = C_Transitive'46'constructor_19 (AgdaAny ->
                                    AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Transitive.Transitive.trans
d_trans_30 ::
  T_Transitive_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_30 v0
  = case coe v0 of
      C_Transitive'46'constructor_19 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Transitive.Transitive._R⟨_⟩_
d__R'10216'_'10217'__38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Transitive_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d__R'10216'_'10217'__38 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du__R'10216'_'10217'__38 v3 v4 v5 v6 v7 v8
du__R'10216'_'10217'__38 ::
  T_Transitive_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du__R'10216'_'10217'__38 v0 v1 v2 v3 v4 v5
  = coe d_trans_30 v0 v1 v2 v3 v4 v5
-- Transitive._._R⟨_⟩_
d__R'10216'_'10217'__48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Transitive_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d__R'10216'_'10217'__48 ~v0 ~v1 ~v2 v3
  = du__R'10216'_'10217'__48 v3
du__R'10216'_'10217'__48 ::
  T_Transitive_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du__R'10216'_'10217'__48 v0 = coe du__R'10216'_'10217'__38 (coe v0)
-- Transitive._.trans
d_trans_50 ::
  T_Transitive_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_50 v0 = coe d_trans_30 (coe v0)
-- Transitive.Transitiveₚ
d_Transitive'8346'_58 a0 a1 a2 = ()
newtype T_Transitive'8346'_58
  = C_Transitive'8346''46'constructor_475 (AgdaAny ->
                                           AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Transitive.Transitiveₚ.transₚ
d_trans'8346'_80 ::
  T_Transitive'8346'_58 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'8346'_80 v0
  = case coe v0 of
      C_Transitive'8346''46'constructor_475 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Transitive.Transitiveₚ._R⟨_⟩ₚ_
d__R'10216'_'10217''8346'__88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Transitive'8346'_58 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d__R'10216'_'10217''8346'__88 = erased
-- Transitive._._R⟨_⟩ₚ_
d__R'10216'_'10217''8346'__98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Transitive'8346'_58 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d__R'10216'_'10217''8346'__98 v0 ~v1 ~v2 v3
  = du__R'10216'_'10217''8346'__98 v0 v3
du__R'10216'_'10217''8346'__98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  T_Transitive'8346'_58 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du__R'10216'_'10217''8346'__98 v0 v1
  = coe d__R'10216'_'10217''8346'__88 v0 erased erased v1
-- Transitive._.transₚ
d_trans'8346'_100 ::
  T_Transitive'8346'_58 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'8346'_100 v0 = coe d_trans'8346'_80 (coe v0)
