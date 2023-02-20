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

module MAlonzo.Code.Antisymmetric where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Equality

-- Antisymmetric.Antisymmetric
d_Antisymmetric_8 a0 a1 a2 = ()
data T_Antisymmetric_8 = C_Antisymmetric'46'constructor_59
-- Antisymmetric.Antisymmetric.asym
d_asym_26 ::
  T_Antisymmetric_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_asym_26 = erased
-- Antisymmetric._.asym
d_asym_30 ::
  T_Antisymmetric_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_asym_30 = erased
-- Antisymmetric.Antisymmetricₚ
d_Antisymmetric'8346'_38 a0 a1 a2 = ()
data T_Antisymmetric'8346'_38
  = C_Antisymmetric'8346''46'constructor_229
-- Antisymmetric.Antisymmetricₚ.asymₚ
d_asym'8346'_56 ::
  T_Antisymmetric'8346'_38 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_asym'8346'_56 = erased
-- Antisymmetric._.asymₚ
d_asym'8346'_60 ::
  T_Antisymmetric'8346'_38 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_asym'8346'_60 = erased
