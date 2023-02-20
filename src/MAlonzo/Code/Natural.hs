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

module MAlonzo.Code.Natural where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Antisymmetric
import qualified MAlonzo.Code.Equality
import qualified MAlonzo.Code.Irreflexive
import qualified MAlonzo.Code.Isomorphism
import qualified MAlonzo.Code.Prelude
import qualified MAlonzo.Code.Reflexive
import qualified MAlonzo.Code.StronglyAntisymmetric
import qualified MAlonzo.Code.Symmetric
import qualified MAlonzo.Code.Transitive

-- Natural.ℕ
d_ℕ_2 = ()
data T_ℕ_2 = C_zero_4 | C_suc_8 Integer
-- Natural.rec
d_rec_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> Integer -> AgdaAny
d_rec_14 ~v0 ~v1 v2 v3 v4 = du_rec_14 v2 v3 v4
du_rec_14 :: AgdaAny -> (AgdaAny -> AgdaAny) -> Integer -> AgdaAny
du_rec_14 v0 v1 v2
  = case coe v2 of
      0 -> coe v0
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe v1 (coe du_rec_14 (coe v0) (coe v1) (coe v3))
-- Natural._+_
d__'43'__26 = ((+) :: Integer -> Integer -> Integer)
-- Natural.rec+
d_rec'43'_38 ::
  Integer -> Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_rec'43'_38 = erased
-- Natural._*_
d__'42'__46 = ((*) :: Integer -> Integer -> Integer)
-- Natural._-_
d__'45'__52
  = ((\ x y -> max 0 (x - y)) :: Integer -> Integer -> Integer)
-- Natural._==_
d__'61''61'__62 = ((==) :: Integer -> Integer -> Bool)
-- Natural._<𝟚_
d__'60'𝟚__68 = ((<) :: Integer -> Integer -> Bool)
-- Natural.div-helper
d_div'45'helper_82
  = ((\ k m n j -> k + div (max 0 $ n + m - j) (m + 1)) :: Integer -> Integer -> Integer -> Integer -> Integer)
-- Natural.mod-helper
d_mod'45'helper_112
  = ((\ k m n j -> if n > j then mod (n - j - 1) (m + 1) else (k + n)) :: Integer -> Integer -> Integer -> Integer -> Integer)
-- Natural._>_
d__'62'__134 a0 a1 = ()
data T__'62'__134 = C_gt_138 | C_gtSuc_144 T__'62'__134
-- Natural._≥_
d__'8805'__146 a0 a1 = ()
data T__'8805'__146 = C_ge_150 | C_geSuc_156 T__'8805'__146
-- Natural._<_
d__'60'__158 a0 a1 = ()
data T__'60'__158 = C_lt_162 | C_ltSuc_168 T__'60'__158
-- Natural._≤_
d__'8804'__170 a0 a1 = ()
data T__'8804'__170 = C_le_174 | C_leSuc_180 T__'8804'__170
-- Natural._≡ℕ_
d__'8801'ℕ__182 a0 a1 = ()
data T__'8801'ℕ__182 = C_eqZero_184 | C_eqSuc_190 T__'8801'ℕ__182
-- Natural.≡ℕ→≡ₛ
d_'8801'ℕ'8594''8801''8347'_196 ::
  Integer ->
  Integer ->
  T__'8801'ℕ__182 -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_'8801'ℕ'8594''8801''8347'_196 = erased
-- Natural.≡ₛ→≡ℕ
d_'8801''8347''8594''8801'ℕ_204 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Equality.T__'8801''8347'__24 -> T__'8801'ℕ__182
d_'8801''8347''8594''8801'ℕ_204 v0 ~v1 ~v2
  = du_'8801''8347''8594''8801'ℕ_204 v0
du_'8801''8347''8594''8801'ℕ_204 :: Integer -> T__'8801'ℕ__182
du_'8801''8347''8594''8801'ℕ_204 v0
  = case coe v0 of
      0 -> coe C_eqZero_184
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe C_eqSuc_190 (coe du_'8801''8347''8594''8801'ℕ_204 (coe v1))
-- Natural.≡ℕ≅≡ₛ
d_'8801'ℕ'8773''8801''8347'_212 ::
  Integer -> Integer -> MAlonzo.Code.Isomorphism.T__'8773'__8
d_'8801'ℕ'8773''8801''8347'_212 v0 ~v1
  = du_'8801'ℕ'8773''8801''8347'_212 v0
du_'8801'ℕ'8773''8801''8347'_212 ::
  Integer -> MAlonzo.Code.Isomorphism.T__'8773'__8
du_'8801'ℕ'8773''8801''8347'_212 v0
  = coe
      MAlonzo.Code.Isomorphism.C__'8773'_'46'constructor_475 erased
      (\ v1 -> coe du_'8801''8347''8594''8801'ℕ_204 (coe v0))
-- Natural._.f'
d_f''_224 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Equality.T__'8801''8347'__24 ->
  MAlonzo.Code.Equality.T__'8801''8347'__24
d_f''_224 = erased
-- Natural._.g'
d_g''_234 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  T__'8801'ℕ__182 -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_g''_234 = erased
-- Natural._._.p
d_p_248 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  T__'8801'ℕ__182 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Equality.T__'8801''8347'__24 ->
  MAlonzo.Code.Equality.T__'8801''8347'__24
d_p_248 = erased
-- Natural.≤≥≡ℕ
d_'8804''8805''8801'ℕ_256 ::
  Integer ->
  Integer -> T__'8804'__170 -> T__'8804'__170 -> T__'8801'ℕ__182
d_'8804''8805''8801'ℕ_256 ~v0 ~v1 v2 v3
  = du_'8804''8805''8801'ℕ_256 v2 v3
du_'8804''8805''8801'ℕ_256 ::
  T__'8804'__170 -> T__'8804'__170 -> T__'8801'ℕ__182
du_'8804''8805''8801'ℕ_256 v0 v1
  = case coe v0 of
      C_le_174 -> coe seq (coe v1) (coe C_eqZero_184)
      C_leSuc_180 v4
        -> case coe v1 of
             C_leSuc_180 v7
               -> coe
                    C_eqSuc_190 (coe du_'8804''8805''8801'ℕ_256 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Natural.≤≥sym
d_'8804''8805'sym_266 ::
  Integer -> Integer -> MAlonzo.Code.Prelude.T_Σ_162
d_'8804''8805'sym_266 v0 v1
  = coe
      MAlonzo.Code.Prelude.C__'44'Σ__180
      (coe d_'46'extendedlambda0_268 (coe v0) (coe v1))
      (coe d_'46'extendedlambda1_272 (coe v0) (coe v1))
-- Natural..extendedlambda0
d_'46'extendedlambda0_268 ::
  Integer -> Integer -> T__'8804'__170 -> T__'8805'__146
d_'46'extendedlambda0_268 v0 v1 v2
  = case coe v2 of
      C_le_174 -> coe C_ge_150
      C_leSuc_180 v5
        -> let v6 = subInt (coe v0) (coe (1 :: Integer)) in
           let v7 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             C_geSuc_156
             (coe
                MAlonzo.Code.Prelude.d_π'8321'_176
                (d_'8804''8805'sym_266 (coe v6) (coe v7)) v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Natural..extendedlambda1
d_'46'extendedlambda1_272 ::
  Integer -> Integer -> T__'8805'__146 -> T__'8804'__170
d_'46'extendedlambda1_272 v0 v1 v2
  = case coe v2 of
      C_ge_150 -> coe C_le_174
      C_geSuc_156 v5
        -> let v6 = subInt (coe v0) (coe (1 :: Integer)) in
           let v7 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             C_leSuc_180
             (coe
                MAlonzo.Code.Prelude.d_π'8322'_178
                (d_'8804''8805'sym_266 (coe v6) (coe v7)) v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Natural.<>sym
d_'60''62'sym_280 ::
  Integer -> Integer -> MAlonzo.Code.Prelude.T_Σ_162
d_'60''62'sym_280 v0 v1
  = coe
      MAlonzo.Code.Prelude.C__'44'Σ__180
      (coe d_'46'extendedlambda2_282 (coe v0) (coe v1))
      (coe d_'46'extendedlambda3_286 (coe v0) (coe v1))
-- Natural..extendedlambda2
d_'46'extendedlambda2_282 ::
  Integer -> Integer -> T__'60'__158 -> T__'62'__134
d_'46'extendedlambda2_282 v0 v1 v2
  = case coe v2 of
      C_lt_162 -> coe C_gt_138
      C_ltSuc_168 v5
        -> let v6 = subInt (coe v0) (coe (1 :: Integer)) in
           let v7 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             C_gtSuc_144
             (coe
                MAlonzo.Code.Prelude.d_π'8321'_176
                (d_'60''62'sym_280 (coe v6) (coe v7)) v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Natural..extendedlambda3
d_'46'extendedlambda3_286 ::
  Integer -> Integer -> T__'62'__134 -> T__'60'__158
d_'46'extendedlambda3_286 v0 v1 v2
  = case coe v2 of
      C_gt_138 -> coe C_lt_162
      C_gtSuc_144 v5
        -> let v6 = subInt (coe v0) (coe (1 :: Integer)) in
           let v7 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             C_ltSuc_168
             (coe
                MAlonzo.Code.Prelude.d_π'8322'_178
                (d_'60''62'sym_280 (coe v6) (coe v7)) v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Natural.≤≅≥
d_'8804''8773''8805'_294 ::
  Integer -> Integer -> MAlonzo.Code.Isomorphism.T__'8773'__8
d_'8804''8773''8805'_294 v0 v1
  = coe
      MAlonzo.Code.Isomorphism.C__'8773'_'46'constructor_475
      (MAlonzo.Code.Prelude.d_π'8321'_176
         (coe d_'8804''8805'sym_266 (coe v0) (coe v1)))
      (MAlonzo.Code.Prelude.d_π'8322'_178
         (coe d_'8804''8805'sym_266 (coe v0) (coe v1)))
-- Natural._.f'
d_f''_306 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  T__'8805'__146 -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_f''_306 = erased
-- Natural._.g'
d_g''_318 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  T__'8804'__170 -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_g''_318 = erased
-- Natural.<≅>
d_'60''8773''62'_328 ::
  Integer -> Integer -> MAlonzo.Code.Isomorphism.T__'8773'__8
d_'60''8773''62'_328 v0 v1
  = coe
      MAlonzo.Code.Isomorphism.C__'8773'_'46'constructor_475
      (MAlonzo.Code.Prelude.d_π'8321'_176
         (coe d_'60''62'sym_280 (coe v0) (coe v1)))
      (MAlonzo.Code.Prelude.d_π'8322'_178
         (coe d_'60''62'sym_280 (coe v0) (coe v1)))
-- Natural._.f'
d_f''_340 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  T__'62'__134 -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_f''_340 = erased
-- Natural._.g'
d_g''_352 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  T__'60'__158 -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_g''_352 = erased
-- Natural.n<k→n≤k
d_n'60'k'8594'n'8804'k_362 ::
  Integer -> Integer -> T__'60'__158 -> T__'8804'__170
d_n'60'k'8594'n'8804'k_362 ~v0 ~v1 v2
  = du_n'60'k'8594'n'8804'k_362 v2
du_n'60'k'8594'n'8804'k_362 :: T__'60'__158 -> T__'8804'__170
du_n'60'k'8594'n'8804'k_362 v0
  = case coe v0 of
      C_lt_162 -> coe C_le_174
      C_ltSuc_168 v3
        -> coe C_leSuc_180 (coe du_n'60'k'8594'n'8804'k_362 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Natural.n≤k→n<k+1
d_n'8804'k'8594'n'60'k'43'1_370 ::
  Integer -> Integer -> T__'8804'__170 -> T__'60'__158
d_n'8804'k'8594'n'60'k'43'1_370 ~v0 ~v1 v2
  = du_n'8804'k'8594'n'60'k'43'1_370 v2
du_n'8804'k'8594'n'60'k'43'1_370 :: T__'8804'__170 -> T__'60'__158
du_n'8804'k'8594'n'60'k'43'1_370 v0
  = case coe v0 of
      C_le_174 -> coe C_lt_162
      C_leSuc_180 v3
        -> coe C_ltSuc_168 (coe du_n'8804'k'8594'n'60'k'43'1_370 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Natural.n>k→n≥k
d_n'62'k'8594'n'8805'k_380 ::
  Integer -> Integer -> T__'62'__134 -> T__'8805'__146
d_n'62'k'8594'n'8805'k_380 ~v0 ~v1 v2
  = du_n'62'k'8594'n'8805'k_380 v2
du_n'62'k'8594'n'8805'k_380 :: T__'62'__134 -> T__'8805'__146
du_n'62'k'8594'n'8805'k_380 v0
  = case coe v0 of
      C_gt_138 -> coe C_ge_150
      C_gtSuc_144 v3
        -> coe C_geSuc_156 (coe du_n'62'k'8594'n'8805'k_380 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Natural.n≥k→n>k+1
d_n'8805'k'8594'n'62'k'43'1_388 ::
  Integer -> Integer -> T__'8805'__146 -> T__'62'__134
d_n'8805'k'8594'n'62'k'43'1_388 ~v0 ~v1 v2
  = du_n'8805'k'8594'n'62'k'43'1_388 v2
du_n'8805'k'8594'n'62'k'43'1_388 :: T__'8805'__146 -> T__'62'__134
du_n'8805'k'8594'n'62'k'43'1_388 v0
  = case coe v0 of
      C_ge_150 -> coe C_gt_138
      C_geSuc_156 v3
        -> coe C_gtSuc_144 (coe du_n'8805'k'8594'n'62'k'43'1_388 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Natural.<Trans
d_'60'Trans_394 :: MAlonzo.Code.Transitive.T_Transitive_8
d_'60'Trans_394
  = coe
      MAlonzo.Code.Transitive.C_Transitive'46'constructor_19
      (\ v0 v1 v2 v3 v4 -> coe du_trans'60'_406 v3 v4)
-- Natural._.trans<
d_trans'60'_406 ::
  Integer ->
  Integer -> Integer -> T__'60'__158 -> T__'60'__158 -> T__'60'__158
d_trans'60'_406 ~v0 ~v1 ~v2 v3 v4 = du_trans'60'_406 v3 v4
du_trans'60'_406 :: T__'60'__158 -> T__'60'__158 -> T__'60'__158
du_trans'60'_406 v0 v1
  = case coe v0 of
      C_lt_162 -> coe seq (coe v1) (coe C_lt_162)
      C_ltSuc_168 v4
        -> case coe v1 of
             C_ltSuc_168 v7
               -> coe C_ltSuc_168 (coe du_trans'60'_406 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Natural.≤Trans
d_'8804'Trans_414 :: MAlonzo.Code.Transitive.T_Transitive_8
d_'8804'Trans_414
  = coe
      MAlonzo.Code.Transitive.C_Transitive'46'constructor_19
      (\ v0 v1 v2 v3 v4 -> coe du_trans'8804'_426 v3 v4)
-- Natural._.trans≤
d_trans'8804'_426 ::
  Integer ->
  Integer ->
  Integer -> T__'8804'__170 -> T__'8804'__170 -> T__'8804'__170
d_trans'8804'_426 ~v0 ~v1 ~v2 v3 v4 = du_trans'8804'_426 v3 v4
du_trans'8804'_426 ::
  T__'8804'__170 -> T__'8804'__170 -> T__'8804'__170
du_trans'8804'_426 v0 v1
  = case coe v0 of
      C_le_174 -> coe C_le_174
      C_leSuc_180 v4
        -> case coe v1 of
             C_leSuc_180 v7
               -> coe C_leSuc_180 (coe du_trans'8804'_426 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Natural.>Trans
d_'62'Trans_434 :: MAlonzo.Code.Transitive.T_Transitive_8
d_'62'Trans_434
  = coe
      MAlonzo.Code.Transitive.C_Transitive'46'constructor_19
      (\ v0 v1 v2 v3 v4 -> coe du_trans'62'_446 v3 v4)
-- Natural._.trans>
d_trans'62'_446 ::
  Integer ->
  Integer -> Integer -> T__'62'__134 -> T__'62'__134 -> T__'62'__134
d_trans'62'_446 ~v0 ~v1 ~v2 v3 v4 = du_trans'62'_446 v3 v4
du_trans'62'_446 :: T__'62'__134 -> T__'62'__134 -> T__'62'__134
du_trans'62'_446 v0 v1
  = case coe v0 of
      C_gtSuc_144 v4
        -> case coe v1 of
             C_gt_138 -> coe C_gt_138
             C_gtSuc_144 v7
               -> coe C_gtSuc_144 (coe du_trans'62'_446 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Natural.≥Trans
d_'8805'Trans_454 :: MAlonzo.Code.Transitive.T_Transitive_8
d_'8805'Trans_454
  = coe
      MAlonzo.Code.Transitive.C_Transitive'46'constructor_19
      (\ v0 v1 v2 v3 v4 -> coe du_trans'8805'_466 v3 v4)
-- Natural._.trans≥
d_trans'8805'_466 ::
  Integer ->
  Integer ->
  Integer -> T__'8805'__146 -> T__'8805'__146 -> T__'8805'__146
d_trans'8805'_466 ~v0 ~v1 ~v2 v3 v4 = du_trans'8805'_466 v3 v4
du_trans'8805'_466 ::
  T__'8805'__146 -> T__'8805'__146 -> T__'8805'__146
du_trans'8805'_466 v0 v1
  = case coe v1 of
      C_ge_150 -> coe C_ge_150
      C_geSuc_156 v4
        -> case coe v0 of
             C_geSuc_156 v7
               -> coe C_geSuc_156 (coe du_trans'8805'_466 (coe v7) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Natural.≡ℕTrans
d_'8801'ℕTrans_474 :: MAlonzo.Code.Transitive.T_Transitive_8
d_'8801'ℕTrans_474
  = coe
      MAlonzo.Code.Transitive.C_Transitive'46'constructor_19
      (\ v0 v1 v2 v3 v4 -> coe du_trans'8801'ℕ_486 v3 v4)
-- Natural._.trans≡ℕ
d_trans'8801'ℕ_486 ::
  Integer ->
  Integer ->
  Integer -> T__'8801'ℕ__182 -> T__'8801'ℕ__182 -> T__'8801'ℕ__182
d_trans'8801'ℕ_486 ~v0 ~v1 ~v2 v3 v4 = du_trans'8801'ℕ_486 v3 v4
du_trans'8801'ℕ_486 ::
  T__'8801'ℕ__182 -> T__'8801'ℕ__182 -> T__'8801'ℕ__182
du_trans'8801'ℕ_486 v0 v1
  = case coe v0 of
      C_eqZero_184 -> coe seq (coe v1) (coe v0)
      C_eqSuc_190 v4
        -> case coe v1 of
             C_eqSuc_190 v7
               -> coe C_eqSuc_190 (coe du_trans'8801'ℕ_486 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Natural._≤⟨_⟩_
d__'8804''10216'_'10217'__500 ::
  Integer ->
  Integer ->
  Integer -> T__'8804'__170 -> T__'8804'__170 -> T__'8804'__170
d__'8804''10216'_'10217'__500 ~v0 ~v1 ~v2 v3 v4
  = du__'8804''10216'_'10217'__500 v3 v4
du__'8804''10216'_'10217'__500 ::
  T__'8804'__170 -> T__'8804'__170 -> T__'8804'__170
du__'8804''10216'_'10217'__500 v0 v1
  = coe du_trans'8804'_426 (coe v0) (coe v1)
-- Natural._<⟨_⟩_
d__'60''10216'_'10217'__516 ::
  Integer ->
  Integer -> Integer -> T__'60'__158 -> T__'60'__158 -> T__'60'__158
d__'60''10216'_'10217'__516 ~v0 ~v1 ~v2 v3 v4
  = du__'60''10216'_'10217'__516 v3 v4
du__'60''10216'_'10217'__516 ::
  T__'60'__158 -> T__'60'__158 -> T__'60'__158
du__'60''10216'_'10217'__516 v0 v1
  = coe du_trans'60'_406 (coe v0) (coe v1)
-- Natural._>⟨_⟩_
d__'62''10216'_'10217'__532 ::
  Integer ->
  Integer -> Integer -> T__'62'__134 -> T__'62'__134 -> T__'62'__134
d__'62''10216'_'10217'__532 ~v0 ~v1 ~v2 v3 v4
  = du__'62''10216'_'10217'__532 v3 v4
du__'62''10216'_'10217'__532 ::
  T__'62'__134 -> T__'62'__134 -> T__'62'__134
du__'62''10216'_'10217'__532 v0 v1
  = coe du_trans'62'_446 (coe v0) (coe v1)
-- Natural._≥⟨_⟩_
d__'8805''10216'_'10217'__548 ::
  Integer ->
  Integer ->
  Integer -> T__'8805'__146 -> T__'8805'__146 -> T__'8805'__146
d__'8805''10216'_'10217'__548 ~v0 ~v1 ~v2 v3 v4
  = du__'8805''10216'_'10217'__548 v3 v4
du__'8805''10216'_'10217'__548 ::
  T__'8805'__146 -> T__'8805'__146 -> T__'8805'__146
du__'8805''10216'_'10217'__548 v0 v1
  = coe du_trans'8805'_466 (coe v0) (coe v1)
-- Natural._≡ℕ⟨_⟩_
d__'8801'ℕ'10216'_'10217'__564 ::
  Integer ->
  Integer ->
  Integer -> T__'8801'ℕ__182 -> T__'8801'ℕ__182 -> T__'8801'ℕ__182
d__'8801'ℕ'10216'_'10217'__564 ~v0 ~v1 ~v2 v3 v4
  = du__'8801'ℕ'10216'_'10217'__564 v3 v4
du__'8801'ℕ'10216'_'10217'__564 ::
  T__'8801'ℕ__182 -> T__'8801'ℕ__182 -> T__'8801'ℕ__182
du__'8801'ℕ'10216'_'10217'__564 v0 v1
  = coe du_trans'8801'ℕ_486 (coe v0) (coe v1)
-- Natural.≤Refl
d_'8804'Refl_572 :: MAlonzo.Code.Reflexive.T_Reflexive_8
d_'8804'Refl_572
  = coe
      MAlonzo.Code.Reflexive.C_Reflexive'46'constructor_7 (coe d_r_580)
-- Natural._.r
d_r_580 :: Integer -> T__'8804'__170
d_r_580 v0
  = case coe v0 of
      0 -> coe C_le_174
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe C_leSuc_180 (d_r_580 (coe v1))
-- Natural.≥Refl
d_'8805'Refl_584 :: MAlonzo.Code.Reflexive.T_Reflexive_8
d_'8805'Refl_584
  = coe
      MAlonzo.Code.Reflexive.C_Reflexive'46'constructor_7 (coe d_r_592)
-- Natural._.r
d_r_592 :: Integer -> T__'8805'__146
d_r_592 v0
  = case coe v0 of
      0 -> coe C_ge_150
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe C_geSuc_156 (d_r_592 (coe v1))
-- Natural.≡ℕRefl
d_'8801'ℕRefl_596 :: MAlonzo.Code.Reflexive.T_Reflexive_8
d_'8801'ℕRefl_596
  = coe
      MAlonzo.Code.Reflexive.C_Reflexive'46'constructor_7 (coe d_r_604)
-- Natural._.r
d_r_604 :: Integer -> T__'8801'ℕ__182
d_r_604 v0
  = case coe v0 of
      0 -> coe C_eqZero_184
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe C_eqSuc_190 (d_r_604 (coe v1))
-- Natural.<Irrefl
d_'60'Irrefl_608 :: MAlonzo.Code.Irreflexive.T_Irreflexive_8
d_'60'Irrefl_608 = erased
-- Natural._.r
d_r_616 ::
  Integer -> T__'60'__158 -> MAlonzo.Code.Prelude.T_'8869'_222
d_r_616 = erased
-- Natural.>Irrefl
d_'62'Irrefl_620 :: MAlonzo.Code.Irreflexive.T_Irreflexive_8
d_'62'Irrefl_620 = erased
-- Natural._.r
d_r_628 ::
  Integer -> T__'62'__134 -> MAlonzo.Code.Prelude.T_'8869'_222
d_r_628 = erased
-- Natural.≡ℕSym
d_'8801'ℕSym_632 :: MAlonzo.Code.Symmetric.T_Symmetric_8
d_'8801'ℕSym_632
  = coe
      MAlonzo.Code.Symmetric.C_Symmetric'46'constructor_13
      (coe (\ v0 v1 v2 -> v2))
-- Natural._.s
d_s_642 :: Integer -> Integer -> T__'8801'ℕ__182 -> T__'8801'ℕ__182
d_s_642 ~v0 ~v1 v2 = du_s_642 v2
du_s_642 :: T__'8801'ℕ__182 -> T__'8801'ℕ__182
du_s_642 v0 = coe v0
-- Natural.≤Antisym
d_'8804'Antisym_646 :: MAlonzo.Code.Antisymmetric.T_Antisymmetric_8
d_'8804'Antisym_646 = erased
-- Natural._.asy
d_asy_656 ::
  Integer ->
  Integer ->
  T__'8804'__170 ->
  T__'8804'__170 -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_asy_656 = erased
-- Natural.≥Antisym
d_'8805'Antisym_666 :: MAlonzo.Code.Antisymmetric.T_Antisymmetric_8
d_'8805'Antisym_666 = erased
-- Natural._.asy
d_asy_676 ::
  Integer ->
  Integer ->
  T__'8805'__146 ->
  T__'8805'__146 -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_asy_676 = erased
-- Natural.<StrongAntisym
d_'60'StrongAntisym_686 ::
  MAlonzo.Code.StronglyAntisymmetric.T_StronglyAntisymmetric_8
d_'60'StrongAntisym_686 = erased
-- Natural._.sasy
d_sasy_696 ::
  Integer ->
  Integer ->
  T__'60'__158 -> T__'60'__158 -> MAlonzo.Code.Prelude.T_'8869'_222
d_sasy_696 = erased
-- Natural.>StrongAntisym
d_'62'StrongAntisym_702 ::
  MAlonzo.Code.StronglyAntisymmetric.T_StronglyAntisymmetric_8
d_'62'StrongAntisym_702 = erased
-- Natural._.sasy
d_sasy_712 ::
  Integer ->
  Integer ->
  T__'62'__134 -> T__'62'__134 -> MAlonzo.Code.Prelude.T_'8869'_222
d_sasy_712 = erased
-- Natural.idr+
d_idr'43'_720 ::
  Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_idr'43'_720 = erased
-- Natural.sucr+
d_sucr'43'_728 ::
  Integer -> Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_sucr'43'_728 = erased
-- Natural.idl+
d_idl'43'_738 ::
  Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_idl'43'_738 = erased
-- Natural.assoc+
d_assoc'43'_748 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_assoc'43'_748 = erased
-- Natural.comm+
d_comm'43'_764 ::
  Integer -> Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_comm'43'_764 = erased
-- Natural.idl*
d_idl'42'_774 ::
  Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_idl'42'_774 = erased
-- Natural.idr*
d_idr'42'_778 ::
  Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_idr'42'_778 = erased
-- Natural.sucl*
d_sucl'42'_788 ::
  Integer -> Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_sucl'42'_788 = erased
-- Natural.sucr*
d_sucr'42'_794 ::
  Integer -> Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_sucr'42'_794 = erased
-- Natural.distr*+
d_distr'42''43'_814 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_distr'42''43'_814 = erased
-- Natural.distr+*
d_distr'43''42'_840 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_distr'43''42'_840 = erased
-- Natural.assoc*
d_assoc'42'_862 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_assoc'42'_862 = erased
-- Natural.zero*β₁
d_zero'42'β'8321'_880 ::
  Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_zero'42'β'8321'_880 = erased
-- Natural.zero*β₂
d_zero'42'β'8322'_886 ::
  Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_zero'42'β'8322'_886 = erased
-- Natural.comm*
d_comm'42'_896 ::
  Integer -> Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_comm'42'_896 = erased
-- Natural.idr-
d_idr'45'_910 ::
  Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_idr'45'_910 = erased
-- Natural.suc-1
d_suc'45'1_914 ::
  Integer -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_suc'45'1_914 = erased
-- Natural.k-1+1
d_k'45'1'43'1_918 ::
  Integer ->
  T__'62'__134 -> MAlonzo.Code.Equality.T__'8801''8347'__24
d_k'45'1'43'1_918 = erased
-- Natural.suc<
d_suc'60'_924 :: Integer -> T__'60'__158
d_suc'60'_924 v0
  = case coe v0 of
      0 -> coe C_lt_162
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe C_ltSuc_168 (d_suc'60'_924 (coe v1))
-- Natural.suc≤
d_suc'8804'_930 :: Integer -> T__'8804'__170
d_suc'8804'_930 v0
  = case coe v0 of
      0 -> coe C_le_174
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe C_leSuc_180 (d_suc'8804'_930 (coe v1))
-- Natural.suc≥
d_suc'8805'_936 :: Integer -> T__'8805'__146
d_suc'8805'_936 v0
  = case coe v0 of
      0 -> coe C_ge_150
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe C_geSuc_156 (d_suc'8805'_936 (coe v1))
-- Natural.suc>
d_suc'62'_942 :: Integer -> T__'62'__134
d_suc'62'_942 v0
  = case coe v0 of
      0 -> coe C_gt_138
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe C_gtSuc_144 (d_suc'62'_942 (coe v1))
-- Natural.1≠0
d_1'8800'0_946 ::
  T__'8801'ℕ__182 -> MAlonzo.Code.Prelude.T_'8869'_222
d_1'8800'0_946 = erased
-- Natural.isOdd
d_isOdd_948 :: Integer -> ()
d_isOdd_948 = erased
-- Natural.isOdd'
d_isOdd''_954 :: Integer -> ()
d_isOdd''_954 = erased
-- Natural.isOdd''
d_isOdd''''_958 :: Integer -> ()
d_isOdd''''_958 = erased
-- Natural.isEven''
d_isEven''''_960 :: Integer -> ()
d_isEven''''_960 = erased
-- Natural.IsOdd
d_IsOdd_966 a0 = ()
data T_IsOdd_966
  = C_base'45'case_968 | C_inductive'45'step_972 Integer T_IsOdd_966
-- Natural.five-isOdd
d_five'45'isOdd_974 :: MAlonzo.Code.Prelude.T_Σ_162
d_five'45'isOdd_974
  = coe
      MAlonzo.Code.Prelude.C__'44'Σ__180 (coe (2 :: Integer)) erased
-- Natural.five-isOdd'
d_five'45'isOdd''_976 ::
  ((((MAlonzo.Code.Prelude.T_'8869'_222 ->
      MAlonzo.Code.Prelude.T_'8869'_222) ->
     MAlonzo.Code.Prelude.T_'8869'_222) ->
    MAlonzo.Code.Prelude.T_'8869'_222) ->
   MAlonzo.Code.Prelude.T_'8869'_222) ->
  MAlonzo.Code.Prelude.T_'8869'_222
d_five'45'isOdd''_976 = erased
-- Natural.five-isOdd''
d_five'45'isOdd''''_984 :: MAlonzo.Code.Prelude.T_'8868'_244
d_five'45'isOdd''''_984 = erased
-- Natural.five-isOdd'''
d_five'45'isOdd''''''_986 :: T_IsOdd_966
d_five'45'isOdd''''''_986
  = coe
      C_inductive'45'step_972 (coe (3 :: Integer))
      (coe
         C_inductive'45'step_972 (coe (1 :: Integer))
         (coe C_base'45'case_968))
