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

module MAlonzo.Code.Symmetric where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Symmetric.Symmetric
d_Symmetric_8 a0 a1 a2 = ()
newtype T_Symmetric_8
  = C_Symmetric'46'constructor_13 (AgdaAny ->
                                   AgdaAny -> AgdaAny -> AgdaAny)
-- Symmetric.Symmetric.sym
d_sym_26 ::
  T_Symmetric_8 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_26 v0
  = case coe v0 of
      C_Symmetric'46'constructor_13 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Symmetric._.sym
d_sym_30 ::
  T_Symmetric_8 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_30 v0 = coe d_sym_26 (coe v0)
-- Symmetric.Symmetricₚ
d_Symmetric'8346'_38 a0 a1 a2 = ()
newtype T_Symmetric'8346'_38
  = C_Symmetric'8346''46'constructor_129 (AgdaAny ->
                                          AgdaAny -> AgdaAny -> AgdaAny)
-- Symmetric.Symmetricₚ.symₚ
d_sym'8346'_56 ::
  T_Symmetric'8346'_38 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym'8346'_56 v0
  = case coe v0 of
      C_Symmetric'8346''46'constructor_129 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Symmetric._.symₚ
d_sym'8346'_60 ::
  T_Symmetric'8346'_38 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym'8346'_60 v0 = coe d_sym'8346'_56 (coe v0)
