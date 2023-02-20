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

module MAlonzo.Code.Reflexive where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Reflexive.Reflexive
d_Reflexive_8 a0 a1 a2 = ()
newtype T_Reflexive_8
  = C_Reflexive'46'constructor_7 (AgdaAny -> AgdaAny)
-- Reflexive.Reflexive.reflexive
d_reflexive_22 :: T_Reflexive_8 -> AgdaAny -> AgdaAny
d_reflexive_22 v0
  = case coe v0 of
      C_Reflexive'46'constructor_7 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflexive._.reflexive
d_reflexive_26 :: T_Reflexive_8 -> AgdaAny -> AgdaAny
d_reflexive_26 v0 = coe d_reflexive_22 (coe v0)
-- Reflexive.Reflexiveₚ
d_Reflexive'8346'_34 a0 a1 a2 = ()
newtype T_Reflexive'8346'_34
  = C_Reflexive'8346''46'constructor_111 (AgdaAny -> AgdaAny)
-- Reflexive.Reflexiveₚ.reflexiveₚ
d_reflexive'8346'_48 :: T_Reflexive'8346'_34 -> AgdaAny -> AgdaAny
d_reflexive'8346'_48 v0
  = case coe v0 of
      C_Reflexive'8346''46'constructor_111 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflexive._.reflexiveₚ
d_reflexive'8346'_52 :: T_Reflexive'8346'_34 -> AgdaAny -> AgdaAny
d_reflexive'8346'_52 v0 = coe d_reflexive'8346'_48 (coe v0)
