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

module MAlonzo.Code.Bool where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Bool.𝟚
type T_𝟚_2 = Bool
d_𝟚_2 = ()
pattern C_false_4 = False
pattern C_true_6 = True
-- Bool.if_then_else_
d_if_then_else__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> Bool -> AgdaAny -> AgdaAny -> AgdaAny
d_if_then_else__18 ~v0 ~v1 v2 v3 v4 = du_if_then_else__18 v2 v3 v4
du_if_then_else__18 :: Bool -> AgdaAny -> AgdaAny -> AgdaAny
du_if_then_else__18 v0 v1 v2 = if coe v0 then coe v1 else coe v2
-- Bool.dep-if_then_else_
d_dep'45'if_then_else__38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (Bool -> ()) -> Bool -> AgdaAny -> AgdaAny -> AgdaAny
d_dep'45'if_then_else__38 ~v0 ~v1 v2 v3 v4
  = du_dep'45'if_then_else__38 v2 v3 v4
du_dep'45'if_then_else__38 :: Bool -> AgdaAny -> AgdaAny -> AgdaAny
du_dep'45'if_then_else__38 v0 v1 v2
  = if coe v0 then coe v1 else coe v2
-- Bool.ind𝟚
d_ind𝟚_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (Bool -> ()) -> AgdaAny -> AgdaAny -> Bool -> AgdaAny
d_ind𝟚_54 ~v0 ~v1 v2 v3 v4 = du_ind𝟚_54 v2 v3 v4
du_ind𝟚_54 :: AgdaAny -> AgdaAny -> Bool -> AgdaAny
du_ind𝟚_54 v0 v1 v2 = if coe v2 then coe v0 else coe v1
-- Bool._∧_
d__'8743'__68 :: Bool -> Bool -> Bool
d__'8743'__68 v0 v1 = if coe v0 then coe v1 else coe v0
-- Bool._∨_
d__'8744'__74 :: Bool -> Bool -> Bool
d__'8744'__74 v0 v1 = if coe v0 then coe v0 else coe v1
-- Bool._⊃_
d__'8835'__80 :: Bool -> Bool -> Bool
d__'8835'__80 v0 v1 = if coe v0 then coe v1 else coe C_true_6
