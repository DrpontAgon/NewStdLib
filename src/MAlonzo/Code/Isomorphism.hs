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

module MAlonzo.Code.Isomorphism where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Equality
import qualified MAlonzo.Code.EquivalenceRelation
import qualified MAlonzo.Code.Reflexive
import qualified MAlonzo.Code.Symmetric
import qualified MAlonzo.Code.Transitive

-- Isomorphism._≅_
d__'8773'__8 a0 a1 a2 = ()
data T__'8773'__8
  = C__'8773'_'46'constructor_475 (AgdaAny -> AgdaAny)
                                  (AgdaAny -> AgdaAny)
-- Isomorphism._≅_.left→right
d_left'8594'right_24 :: T__'8773'__8 -> AgdaAny -> AgdaAny
d_left'8594'right_24 v0
  = case coe v0 of
      C__'8773'_'46'constructor_475 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Isomorphism._≅_.right→left
d_right'8594'left_26 :: T__'8773'__8 -> AgdaAny -> AgdaAny
d_right'8594'left_26 v0
  = case coe v0 of
      C__'8773'_'46'constructor_475 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Isomorphism._≅_.→∘←≡id
d_'8594''8728''8592''8801'id_28 ::
  T__'8773'__8 -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_'8594''8728''8592''8801'id_28 = erased
-- Isomorphism._≅_.←∘→≡id
d_'8592''8728''8594''8801'id_30 ::
  T__'8773'__8 -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_'8592''8728''8594''8801'id_30 = erased
-- Isomorphism.isoRefl
d_isoRefl_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> T__'8773'__8
d_isoRefl_36 ~v0 ~v1 = du_isoRefl_36
du_isoRefl_36 :: T__'8773'__8
du_isoRefl_36
  = coe C__'8773'_'46'constructor_475 (\ v0 -> v0) (\ v0 -> v0)
-- Isomorphism.≅Refl
d_'8773'Refl_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Reflexive.T_Reflexive_8
d_'8773'Refl_44 ~v0 = du_'8773'Refl_44
du_'8773'Refl_44 :: MAlonzo.Code.Reflexive.T_Reflexive_8
du_'8773'Refl_44
  = coe
      MAlonzo.Code.Reflexive.C_Reflexive'46'constructor_7
      (\ v0 -> coe du_isoRefl_36)
-- Isomorphism.isoSym
d_isoSym_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> T__'8773'__8 -> T__'8773'__8
d_isoSym_52 ~v0 ~v1 ~v2 v3 = du_isoSym_52 v3
du_isoSym_52 :: T__'8773'__8 -> T__'8773'__8
du_isoSym_52 v0
  = case coe v0 of
      C__'8773'_'46'constructor_475 v1 v2
        -> coe C__'8773'_'46'constructor_475 v2 v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Isomorphism.≅Sym
d_'8773'Sym_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Symmetric.T_Symmetric_8
d_'8773'Sym_64 ~v0 = du_'8773'Sym_64
du_'8773'Sym_64 :: MAlonzo.Code.Symmetric.T_Symmetric_8
du_'8773'Sym_64
  = coe
      MAlonzo.Code.Symmetric.C_Symmetric'46'constructor_13
      (\ v0 v1 v2 -> coe du_isoSym_52 v2)
-- Isomorphism.isoTrans
d_isoTrans_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> () -> T__'8773'__8 -> T__'8773'__8 -> T__'8773'__8
d_isoTrans_74 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_isoTrans_74 v4 v5
du_isoTrans_74 :: T__'8773'__8 -> T__'8773'__8 -> T__'8773'__8
du_isoTrans_74 v0 v1
  = case coe v0 of
      C__'8773'_'46'constructor_475 v2 v3
        -> case coe v1 of
             C__'8773'_'46'constructor_475 v6 v7
               -> coe
                    C__'8773'_'46'constructor_475 (\ v10 -> coe v6 (coe v2 v10))
                    (\ v10 -> coe v3 (coe v7 v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Isomorphism._.fgid
d_fgid_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Equality.T__'8801''8347'__24 ->
  MAlonzo.Code.Equality.T__'8801''8347'__24 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Equality.T__'8801''8347'__24 ->
  MAlonzo.Code.Equality.T__'8801''8347'__24 ->
  AgdaAny -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_fgid_106 = erased
-- Isomorphism._.gfid
d_gfid_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Equality.T__'8801''8347'__24 ->
  MAlonzo.Code.Equality.T__'8801''8347'__24 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Equality.T__'8801''8347'__24 ->
  MAlonzo.Code.Equality.T__'8801''8347'__24 ->
  AgdaAny -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_gfid_114 = erased
-- Isomorphism.≅Trans
d_'8773'Trans_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Transitive.T_Transitive_8
d_'8773'Trans_130 ~v0 = du_'8773'Trans_130
du_'8773'Trans_130 :: MAlonzo.Code.Transitive.T_Transitive_8
du_'8773'Trans_130
  = coe
      MAlonzo.Code.Transitive.C_Transitive'46'constructor_19
      (\ v0 v1 v2 v3 v4 -> coe du_isoTrans_74 v3 v4)
-- Isomorphism.≅EqRel
d_'8773'EqRel_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.EquivalenceRelation.T_EquivalenceRelation_14
d_'8773'EqRel_134 = erased
