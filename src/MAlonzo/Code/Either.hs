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

module MAlonzo.Code.Either where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Either._⊎_
d__'8846'__10 a0 a1 a2 a3 = ()
data T__'8846'__10 = C_ι'8321'_20 AgdaAny | C_ι'8322'_22 AgdaAny
-- Either.case
d_case_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  T__'8846'__10 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny
d_case_42 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 = du_case_42 v6 v7 v8
du_case_42 ::
  T__'8846'__10 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny
du_case_42 v0 v1 v2
  = case coe v0 of
      C_ι'8321'_20 v3 -> coe v1 v3
      C_ι'8322'_22 v3 -> coe v2 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Either.Dec
d_Dec_60 :: MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_Dec_60 = erased
