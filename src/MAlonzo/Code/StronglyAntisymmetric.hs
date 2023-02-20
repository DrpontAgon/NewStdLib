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

module MAlonzo.Code.StronglyAntisymmetric where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Antisymmetric
import qualified MAlonzo.Code.Equality
import qualified MAlonzo.Code.Prelude

-- StronglyAntisymmetric.StronglyAntisymmetric
d_StronglyAntisymmetric_8 a0 a1 a2 = ()
data T_StronglyAntisymmetric_8
  = C_StronglyAntisymmetric'46'constructor_35
-- StronglyAntisymmetric.StronglyAntisymmetric.strong-asym
d_strong'45'asym_26 ::
  T_StronglyAntisymmetric_8 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Prelude.T_'8869'_222
d_strong'45'asym_26 = erased
-- StronglyAntisymmetric.StronglyAntisymmetric.weak-asym
d_weak'45'asym_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_StronglyAntisymmetric_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_weak'45'asym_32 = erased
-- StronglyAntisymmetric._.strong-asym
d_strong'45'asym_38 ::
  T_StronglyAntisymmetric_8 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Prelude.T_'8869'_222
d_strong'45'asym_38 = erased
-- StronglyAntisymmetric._.weak-asym
d_weak'45'asym_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_StronglyAntisymmetric_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_weak'45'asym_40 = erased
-- StronglyAntisymmetric.StronglyAntisymmetricₚ
d_StronglyAntisymmetric'8346'_48 a0 a1 a2 = ()
data T_StronglyAntisymmetric'8346'_48
  = C_StronglyAntisymmetric'8346''46'constructor_827
-- StronglyAntisymmetric.StronglyAntisymmetricₚ.strong-asymₚ
d_strong'45'asym'8346'_66 ::
  T_StronglyAntisymmetric'8346'_48 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Prelude.T_'8869''8346'_224
d_strong'45'asym'8346'_66 = erased
-- StronglyAntisymmetric.StronglyAntisymmetricₚ.weak-asymₚ
d_weak'45'asym'8346'_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_StronglyAntisymmetric'8346'_48 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_weak'45'asym'8346'_72 = erased
-- StronglyAntisymmetric._.strong-asymₚ
d_strong'45'asym'8346'_80 ::
  T_StronglyAntisymmetric'8346'_48 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Prelude.T_'8869''8346'_224
d_strong'45'asym'8346'_80 = erased
-- StronglyAntisymmetric._.weak-asymₚ
d_weak'45'asym'8346'_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_StronglyAntisymmetric'8346'_48 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_weak'45'asym'8346'_82 = erased
-- StronglyAntisymmetric.StrongAsym→Asym
d_StrongAsym'8594'Asym_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_StronglyAntisymmetric_8 ->
  MAlonzo.Code.Antisymmetric.T_Antisymmetric_8
d_StrongAsym'8594'Asym_90 = erased
-- StronglyAntisymmetric.StrongAsym→Asymₚ
d_StrongAsym'8594'Asym'8346'_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_StronglyAntisymmetric'8346'_48 ->
  MAlonzo.Code.Antisymmetric.T_Antisymmetric'8346'_38
d_StrongAsym'8594'Asym'8346'_104 = erased
