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

module MAlonzo.Code.Vector where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Bool
import qualified MAlonzo.Code.Equality
import qualified MAlonzo.Code.Fin
import qualified MAlonzo.Code.FunctorApplicativeSelectiveMonad
import qualified MAlonzo.Code.Natural
import qualified MAlonzo.Code.Prelude

-- Vector.Vector
d_Vector_4 a0 a1 = ()
data T_Vector_4 = C_'91''93'_8 | C__'58''58'__12 AgdaAny T_Vector_4
-- Vector.head
d_head_18 :: () -> Integer -> T_Vector_4 -> AgdaAny
d_head_18 ~v0 ~v1 v2 = du_head_18 v2
du_head_18 :: T_Vector_4 -> AgdaAny
du_head_18 v0
  = case coe v0 of
      C__'58''58'__12 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Vector.tail
d_tail_26 :: () -> Integer -> T_Vector_4 -> T_Vector_4
d_tail_26 ~v0 ~v1 v2 = du_tail_26 v2
du_tail_26 :: T_Vector_4 -> T_Vector_4
du_tail_26 v0
  = case coe v0 of
      C__'58''58'__12 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Vector.init
d_init_34 :: () -> Integer -> T_Vector_4 -> T_Vector_4
d_init_34 ~v0 v1 v2 = du_init_34 v1 v2
du_init_34 :: Integer -> T_Vector_4 -> T_Vector_4
du_init_34 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             C__'58''58'__12 v3 v4 -> coe seq (coe v4) (coe C_'91''93'_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             C__'58''58'__12 v4 v5
               -> coe C__'58''58'__12 v4 (coe du_init_34 (coe v2) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
-- Vector.last
d_last_46 :: () -> Integer -> T_Vector_4 -> AgdaAny
d_last_46 ~v0 v1 v2 = du_last_46 v1 v2
du_last_46 :: Integer -> T_Vector_4 -> AgdaAny
du_last_46 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             C__'58''58'__12 v3 v4 -> coe seq (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v1 of
             C__'58''58'__12 v4 v5 -> coe du_last_46 (coe v2) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
-- Vector._++_
d__'43''43'__60 ::
  () -> Integer -> Integer -> T_Vector_4 -> T_Vector_4 -> T_Vector_4
d__'43''43'__60 ~v0 ~v1 ~v2 v3 v4 = du__'43''43'__60 v3 v4
du__'43''43'__60 :: T_Vector_4 -> T_Vector_4 -> T_Vector_4
du__'43''43'__60 v0 v1
  = case coe v0 of
      C_'91''93'_8 -> coe v1
      C__'58''58'__12 v3 v4
        -> coe C__'58''58'__12 v3 (coe du__'43''43'__60 (coe v4) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Vector._!!_
d__'33''33'__74 ::
  () -> Integer -> T_Vector_4 -> MAlonzo.Code.Fin.T_Fin_2 -> AgdaAny
d__'33''33'__74 ~v0 ~v1 v2 v3 = du__'33''33'__74 v2 v3
du__'33''33'__74 ::
  T_Vector_4 -> MAlonzo.Code.Fin.T_Fin_2 -> AgdaAny
du__'33''33'__74 v0 v1
  = case coe v0 of
      C__'58''58'__12 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Fin.C_zero_6 -> coe v3
             MAlonzo.Code.Fin.C_suc_10 v6
               -> case coe v4 of
                    C__'58''58'__12 v8 v9
                      -> coe du__'33''33'__74 (coe C__'58''58'__12 v8 v9) (coe v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Vector.replicate
d_replicate_92 :: () -> Integer -> AgdaAny -> T_Vector_4
d_replicate_92 ~v0 v1 v2 = du_replicate_92 v1 v2
du_replicate_92 :: Integer -> AgdaAny -> T_Vector_4
du_replicate_92 v0 v1
  = case coe v0 of
      0 -> coe C_'91''93'_8
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe C__'58''58'__12 v1 (coe du_replicate_92 (coe v2) (coe v1))
-- Vector.reverse
d_reverse_104 :: () -> Integer -> T_Vector_4 -> T_Vector_4
d_reverse_104 ~v0 v1 = du_reverse_104 v1
du_reverse_104 :: Integer -> T_Vector_4 -> T_Vector_4
du_reverse_104 v0
  = coe du_reverseAcc_120 (coe v0) (coe C_'91''93'_8)
-- Vector._.reverseAcc
d_reverseAcc_120 ::
  () ->
  Integer ->
  () -> Integer -> Integer -> T_Vector_4 -> T_Vector_4 -> T_Vector_4
d_reverseAcc_120 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reverseAcc_120 v4 v5 v6
du_reverseAcc_120 ::
  Integer -> T_Vector_4 -> T_Vector_4 -> T_Vector_4
du_reverseAcc_120 v0 v1 v2
  = case coe v0 of
      0 -> coe seq (coe v2) (coe v1)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v2 of
             C__'58''58'__12 v5 v6
               -> coe
                    du_reverseAcc_120 (coe v3) (coe C__'58''58'__12 v5 v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
-- Vector.intersperse
d_intersperse_144 ::
  () -> Integer -> AgdaAny -> T_Vector_4 -> T_Vector_4
d_intersperse_144 ~v0 v1 v2 v3 = du_intersperse_144 v1 v2 v3
du_intersperse_144 ::
  Integer -> AgdaAny -> T_Vector_4 -> T_Vector_4
du_intersperse_144 v0 v1 v2
  = case coe v0 of
      0 -> coe seq (coe v2) (coe C_'91''93'_8)
      1 -> case coe v2 of
             C__'58''58'__12 v4 v5
               -> coe seq (coe v5) (coe C__'58''58'__12 v4 (coe C_'91''93'_8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> case coe v2 of
             C__'58''58'__12 v4 v5
               -> case coe v5 of
                    C__'58''58'__12 v7 v8
                      -> coe
                           C__'58''58'__12 v4
                           (coe
                              C__'58''58'__12 v1
                              (coe
                                 du_intersperse_144 (coe subInt (coe v0) (coe (1 :: Integer)))
                                 (coe v1) (coe C__'58''58'__12 v7 v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
-- Vector._.pr
d_pr_172 ::
  () ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T_Vector_4 -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_pr_172 = erased
-- Vector.count
d_count_180 ::
  () ->
  Integer ->
  (AgdaAny -> Bool) -> T_Vector_4 -> MAlonzo.Code.Prelude.T_Σ_162
d_count_180 ~v0 v1 v2 v3 = du_count_180 v1 v2 v3
du_count_180 ::
  Integer ->
  (AgdaAny -> Bool) -> T_Vector_4 -> MAlonzo.Code.Prelude.T_Σ_162
du_count_180 v0 v1 v2
  = case coe v0 of
      0 -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Prelude.C__'44'Σ__180 (coe (0 :: Integer))
                (coe MAlonzo.Code.Natural.C_le_174))
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v2 of
             C__'58''58'__12 v5 v6
               -> coe
                    MAlonzo.Code.Bool.du_if_then_else__18 (coe v1 v5)
                    (coe
                       MAlonzo.Code.Prelude.C__'44'Σ__180
                       (coe
                          addInt (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Prelude.d_π'8321'_176
                             (coe du_count_180 (coe v3) (coe v1) (coe v6))))
                       (coe
                          MAlonzo.Code.Natural.C_leSuc_180
                          (MAlonzo.Code.Prelude.d_π'8322'_178
                             (coe du_count_180 (coe v3) (coe v1) (coe v6)))))
                    (coe
                       MAlonzo.Code.Prelude.C__'44'Σ__180
                       (coe
                          MAlonzo.Code.Prelude.d_π'8321'_176
                          (coe du_count_180 (coe v3) (coe v1) (coe v6)))
                       (coe
                          MAlonzo.Code.Natural.du_trans'8804'_426
                          (coe
                             MAlonzo.Code.Prelude.d_π'8322'_178
                             (coe du_count_180 (coe v3) (coe v1) (coe v6)))
                          (coe MAlonzo.Code.Natural.d_suc'8804'_930 (coe v3))))
             _ -> MAlonzo.RTE.mazUnreachableError
-- Vector.filter
d_filter_208 ::
  () -> Integer -> (AgdaAny -> Bool) -> T_Vector_4 -> T_Vector_4
d_filter_208 ~v0 ~v1 v2 v3 = du_filter_208 v2 v3
du_filter_208 :: (AgdaAny -> Bool) -> T_Vector_4 -> T_Vector_4
du_filter_208 v0 v1
  = case coe v1 of
      C_'91''93'_8 -> coe v1
      C__'58''58'__12 v3 v4
        -> let v5 = coe v0 v3 in
           if coe v5
             then coe C__'58''58'__12 v3 (coe du_filter_208 (coe v0) (coe v4))
             else coe du_filter_208 (coe v0) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Vector.FunctorVector
d_FunctorVector_246 ::
  Integer ->
  MAlonzo.Code.FunctorApplicativeSelectiveMonad.T_Functor_4
d_FunctorVector_246 ~v0 = du_FunctorVector_246
du_FunctorVector_246 ::
  MAlonzo.Code.FunctorApplicativeSelectiveMonad.T_Functor_4
du_FunctorVector_246
  = coe
      MAlonzo.Code.FunctorApplicativeSelectiveMonad.C_Functor'46'constructor_763
      (\ v0 v1 -> coe du_map_260)
-- Vector._.map
d_map_260 ::
  Integer ->
  () ->
  () -> Integer -> (AgdaAny -> AgdaAny) -> T_Vector_4 -> T_Vector_4
d_map_260 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_map_260 v4 v5
du_map_260 :: (AgdaAny -> AgdaAny) -> T_Vector_4 -> T_Vector_4
du_map_260 v0 v1
  = case coe v1 of
      C_'91''93'_8 -> coe v1
      C__'58''58'__12 v3 v4
        -> coe
             C__'58''58'__12 (coe v0 v3) (coe du_map_260 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Vector._.mapId
d_mapId_274 ::
  Integer -> () -> Integer -> MAlonzo.Code.Equality.T__'8801'__8
d_mapId_274 = erased
-- Vector._.compF
d_compF_298 ::
  Integer ->
  () ->
  () ->
  () ->
  Integer ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_Vector_4 -> MAlonzo.Code.Equality.T__'8801'__8
d_compF_298 = erased
