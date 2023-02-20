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

module MAlonzo.Code.EquivalenceRelation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Reflexive
import qualified MAlonzo.Code.Symmetric
import qualified MAlonzo.Code.Transitive

-- EquivalenceRelation.EquivalenceRelation
d_EquivalenceRelation_14 a0 a1 a2 a3 a4 a5 = ()
data T_EquivalenceRelation_14
  = C_EquivalenceRelation'46'constructor_7
-- EquivalenceRelation.EquivalenceRelationₚ
d_EquivalenceRelation'8346'_42 a0 a1 a2 a3 a4 a5 = ()
data T_EquivalenceRelation'8346'_42
  = C_EquivalenceRelation'8346''46'constructor_115
