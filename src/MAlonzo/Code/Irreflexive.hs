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

module MAlonzo.Code.Irreflexive where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Prelude
import qualified MAlonzo.Code.Reflexive

-- Irreflexive.Irreflexive
d_Irreflexive_8 a0 a1 a2 = ()
data T_Irreflexive_8 = C_Irreflexive'46'constructor_25
-- Irreflexive.Irreflexive.irreflexive
d_irreflexive_22 ::
  T_Irreflexive_8 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Prelude.T_'8869'_222
d_irreflexive_22 = erased
-- Irreflexive._.irreflexive
d_irreflexive_26 ::
  T_Irreflexive_8 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Prelude.T_'8869'_222
d_irreflexive_26 = erased
-- Irreflexive.Irreflexiveₚ
d_Irreflexive'8346'_34 a0 a1 a2 = ()
data T_Irreflexive'8346'_34
  = C_Irreflexive'8346''46'constructor_149
-- Irreflexive.Irreflexiveₚ.irreflexiveₚ
d_irreflexive'8346'_48 ::
  T_Irreflexive'8346'_34 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Prelude.T_'8869''8346'_224
d_irreflexive'8346'_48 = erased
-- Irreflexive._.irreflexiveₚ
d_irreflexive'8346'_52 ::
  T_Irreflexive'8346'_34 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Prelude.T_'8869''8346'_224
d_irreflexive'8346'_52 = erased
-- Irreflexive.Refl→¬Irrefl
d_Refl'8594''172'Irrefl_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Reflexive.T_Reflexive_8 ->
  T_Irreflexive_8 -> MAlonzo.Code.Prelude.T_'8869'_222
d_Refl'8594''172'Irrefl_64 = erased
-- Irreflexive.Irrefl→¬Refl
d_Irrefl'8594''172'Refl_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Irreflexive_8 ->
  MAlonzo.Code.Reflexive.T_Reflexive_8 ->
  MAlonzo.Code.Prelude.T_'8869'_222
d_Irrefl'8594''172'Refl_88 = erased
