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

module MAlonzo.Code.FunctorApplicativeSelectiveMonad where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Either
import qualified MAlonzo.Code.Equality
import qualified MAlonzo.Code.Prelude

-- FunctorApplicativeSelectiveMonad.Functor
d_Functor_4 a0 = ()
newtype T_Functor_4
  = C_Functor'46'constructor_763 (() ->
                                  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny)
-- FunctorApplicativeSelectiveMonad.Functor.fmap
d_fmap_34 ::
  T_Functor_4 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_34 v0
  = case coe v0 of
      C_Functor'46'constructor_763 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- FunctorApplicativeSelectiveMonad.Functor.idF
d_idF_38 :: T_Functor_4 -> () -> MAlonzo.Code.Equality.T__'8801'__8
d_idF_38 = erased
-- FunctorApplicativeSelectiveMonad.Functor.∘F
d_'8728'F_50 ::
  T_Functor_4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Equality.T__'8801'__8
d_'8728'F_50 = erased
-- FunctorApplicativeSelectiveMonad.Functor._<$>_
d__'60''36''62'__56 ::
  (() -> ()) ->
  T_Functor_4 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__56 ~v0 v1 ~v2 ~v3 v4 v5
  = du__'60''36''62'__56 v1 v4 v5
du__'60''36''62'__56 ::
  T_Functor_4 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62'__56 v0 v1 v2
  = coe d_fmap_34 v0 erased erased v1 v2
-- FunctorApplicativeSelectiveMonad.Functor._<$_
d__'60''36'__66 ::
  (() -> ()) ->
  T_Functor_4 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__66 ~v0 v1 ~v2 ~v3 v4 v5 = du__'60''36'__66 v1 v4 v5
du__'60''36'__66 :: T_Functor_4 -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__66 v0 v1 v2
  = coe d_fmap_34 v0 erased erased (\ v3 -> v1) v2
-- FunctorApplicativeSelectiveMonad._._<$_
d__'60''36'__74 ::
  (() -> ()) ->
  T_Functor_4 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__74 ~v0 v1 = du__'60''36'__74 v1
du__'60''36'__74 ::
  T_Functor_4 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__74 v0 v1 v2 v3 v4
  = coe du__'60''36'__66 (coe v0) v3 v4
-- FunctorApplicativeSelectiveMonad._._<$>_
d__'60''36''62'__76 ::
  (() -> ()) ->
  T_Functor_4 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__76 ~v0 v1 = du__'60''36''62'__76 v1
du__'60''36''62'__76 ::
  T_Functor_4 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62'__76 v0 v1 v2 v3 v4
  = coe du__'60''36''62'__56 (coe v0) v3 v4
-- FunctorApplicativeSelectiveMonad._.fmap
d_fmap_78 ::
  T_Functor_4 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_78 v0 = coe d_fmap_34 (coe v0)
-- FunctorApplicativeSelectiveMonad._.idF
d_idF_80 :: T_Functor_4 -> () -> MAlonzo.Code.Equality.T__'8801'__8
d_idF_80 = erased
-- FunctorApplicativeSelectiveMonad._.∘F
d_'8728'F_82 ::
  T_Functor_4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Equality.T__'8801'__8
d_'8728'F_82 = erased
-- FunctorApplicativeSelectiveMonad.Applicative
d_Applicative_86 a0 = ()
data T_Applicative_86
  = C_Applicative'46'constructor_3487 T_Functor_4
                                      (() -> AgdaAny -> AgdaAny)
                                      (() -> () -> AgdaAny -> AgdaAny -> AgdaAny)
-- FunctorApplicativeSelectiveMonad.Applicative.functorF
d_functorF_144 :: T_Applicative_86 -> T_Functor_4
d_functorF_144 v0
  = case coe v0 of
      C_Applicative'46'constructor_3487 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- FunctorApplicativeSelectiveMonad.Applicative.pure
d_pure_148 :: T_Applicative_86 -> () -> AgdaAny -> AgdaAny
d_pure_148 v0
  = case coe v0 of
      C_Applicative'46'constructor_3487 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- FunctorApplicativeSelectiveMonad.Applicative._⊛_
d__'8859'__154 ::
  T_Applicative_86 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__154 v0
  = case coe v0 of
      C_Applicative'46'constructor_3487 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- FunctorApplicativeSelectiveMonad.Applicative.idA
d_idA_160 ::
  T_Applicative_86 ->
  () -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_idA_160 = erased
-- FunctorApplicativeSelectiveMonad.Applicative.∘A
d_'8728'A_174 ::
  T_Applicative_86 ->
  () ->
  () ->
  () ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_'8728'A_174 = erased
-- FunctorApplicativeSelectiveMonad.Applicative.homoA
d_homoA_184 ::
  T_Applicative_86 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_homoA_184 = erased
-- FunctorApplicativeSelectiveMonad.Applicative.interchangeA
d_interchangeA_196 ::
  T_Applicative_86 ->
  () ->
  () -> AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_interchangeA_196 = erased
-- FunctorApplicativeSelectiveMonad.Applicative._*>_
d__'42''62'__202 ::
  (() -> ()) ->
  T_Applicative_86 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__202 ~v0 v1 ~v2 ~v3 v4 v5 = du__'42''62'__202 v1 v4 v5
du__'42''62'__202 ::
  T_Applicative_86 -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__202 v0 v1 v2
  = coe
      d__'8859'__154 v0 erased erased
      (coe
         du__'60''36'__66 (coe d_functorF_144 (coe v0)) (coe (\ v3 -> v3))
         (coe v1))
      v2
-- FunctorApplicativeSelectiveMonad.Applicative._<*_
d__'60''42'__212 ::
  (() -> ()) ->
  T_Applicative_86 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__212 ~v0 v1 ~v2 ~v3 v4 v5 = du__'60''42'__212 v1 v4 v5
du__'60''42'__212 ::
  T_Applicative_86 -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__212 v0 v1 v2
  = coe
      d__'8859'__154 v0 erased erased
      (coe
         du__'60''36''62'__56 (coe d_functorF_144 (coe v0))
         (coe (\ v3 v4 -> v3)) (coe v1))
      v2
-- FunctorApplicativeSelectiveMonad._._*>_
d__'42''62'__220 ::
  (() -> ()) ->
  T_Applicative_86 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__220 ~v0 v1 = du__'42''62'__220 v1
du__'42''62'__220 ::
  T_Applicative_86 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__220 v0 v1 v2 v3 v4
  = coe du__'42''62'__202 (coe v0) v3 v4
-- FunctorApplicativeSelectiveMonad._._<*_
d__'60''42'__222 ::
  (() -> ()) ->
  T_Applicative_86 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__222 ~v0 v1 = du__'60''42'__222 v1
du__'60''42'__222 ::
  T_Applicative_86 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__222 v0 v1 v2 v3 v4
  = coe du__'60''42'__212 (coe v0) v3 v4
-- FunctorApplicativeSelectiveMonad._._⊛_
d__'8859'__224 ::
  T_Applicative_86 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__224 v0 = coe d__'8859'__154 (coe v0)
-- FunctorApplicativeSelectiveMonad._.functorF
d_functorF_226 :: T_Applicative_86 -> T_Functor_4
d_functorF_226 v0 = coe d_functorF_144 (coe v0)
-- FunctorApplicativeSelectiveMonad._.homoA
d_homoA_228 ::
  T_Applicative_86 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_homoA_228 = erased
-- FunctorApplicativeSelectiveMonad._.idA
d_idA_230 ::
  T_Applicative_86 ->
  () -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_idA_230 = erased
-- FunctorApplicativeSelectiveMonad._.interchangeA
d_interchangeA_232 ::
  T_Applicative_86 ->
  () ->
  () -> AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_interchangeA_232 = erased
-- FunctorApplicativeSelectiveMonad._.pure
d_pure_234 :: T_Applicative_86 -> () -> AgdaAny -> AgdaAny
d_pure_234 v0 = coe d_pure_148 (coe v0)
-- FunctorApplicativeSelectiveMonad._.∘A
d_'8728'A_236 ::
  T_Applicative_86 ->
  () ->
  () ->
  () ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_'8728'A_236 = erased
-- FunctorApplicativeSelectiveMonad.Selective
d_Selective_240 a0 = ()
data T_Selective_240
  = C_Selective'46'constructor_14349 T_Applicative_86
                                     (() -> () -> AgdaAny -> AgdaAny -> AgdaAny)
-- FunctorApplicativeSelectiveMonad.Selective.applicativeS
d_applicativeS_306 :: T_Selective_240 -> T_Applicative_86
d_applicativeS_306 v0
  = case coe v0 of
      C_Selective'46'constructor_14349 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- FunctorApplicativeSelectiveMonad.Selective.select
d_select_316 ::
  T_Selective_240 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_select_316 v0
  = case coe v0 of
      C_Selective'46'constructor_14349 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- FunctorApplicativeSelectiveMonad.Selective.idS
d_idS_324 ::
  T_Selective_240 ->
  () -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_idS_324 = erased
-- FunctorApplicativeSelectiveMonad.Selective.distr*>S
d_distr'42''62'S_336 ::
  T_Selective_240 ->
  () ->
  () ->
  MAlonzo.Code.Either.T__'8846'__10 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_distr'42''62'S_336 = erased
-- FunctorApplicativeSelectiveMonad.Selective.assocS
d_assocS_366 ::
  T_Selective_240 ->
  () ->
  () ->
  () ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_assocS_366 = erased
-- FunctorApplicativeSelectiveMonad.Selective._<*?_
d__'60''42''63'__376 ::
  (() -> ()) ->
  T_Selective_240 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''63'__376 ~v0 v1 ~v2 ~v3 v4 v5
  = du__'60''42''63'__376 v1 v4 v5
du__'60''42''63'__376 ::
  T_Selective_240 -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42''63'__376 v0 v1 v2
  = coe d_select_316 v0 erased erased v1 v2
-- FunctorApplicativeSelectiveMonad.Selective.branch
d_branch_394 ::
  (() -> ()) ->
  T_Selective_240 ->
  () -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_branch_394 ~v0 v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_branch_394 v1 v5 v6 v7
du_branch_394 ::
  T_Selective_240 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_branch_394 v0 v1 v2 v3
  = coe
      d_select_316 v0 erased erased
      (coe
         d_select_316 v0 erased erased
         (coe
            d_fmap_34 (d_functorF_144 (coe d_applicativeS_306 (coe v0))) erased
            erased
            (\ v4 ->
               coe
                 MAlonzo.Code.Either.du_case_42 (coe v4)
                 (coe MAlonzo.Code.Either.C_ι'8321'_20)
                 (coe
                    MAlonzo.Code.Prelude.du__'8728'__52
                    (coe MAlonzo.Code.Either.C_ι'8322'_22)
                    (coe MAlonzo.Code.Either.C_ι'8321'_20)))
            v1)
         (coe
            d_fmap_34 (d_functorF_144 (coe d_applicativeS_306 (coe v0))) erased
            erased
            (\ v4 v5 -> coe MAlonzo.Code.Either.C_ι'8322'_22 (coe v4 v5)) v2))
      v3
-- FunctorApplicativeSelectiveMonad._._<*?_
d__'60''42''63'__416 ::
  (() -> ()) ->
  T_Selective_240 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''63'__416 ~v0 v1 = du__'60''42''63'__416 v1
du__'60''42''63'__416 ::
  T_Selective_240 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42''63'__416 v0 v1 v2 v3 v4
  = coe du__'60''42''63'__376 (coe v0) v3 v4
-- FunctorApplicativeSelectiveMonad._.applicativeS
d_applicativeS_418 :: T_Selective_240 -> T_Applicative_86
d_applicativeS_418 v0 = coe d_applicativeS_306 (coe v0)
-- FunctorApplicativeSelectiveMonad._.assocS
d_assocS_420 ::
  T_Selective_240 ->
  () ->
  () ->
  () ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_assocS_420 = erased
-- FunctorApplicativeSelectiveMonad._.branch
d_branch_422 ::
  (() -> ()) ->
  T_Selective_240 ->
  () -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_branch_422 ~v0 v1 = du_branch_422 v1
du_branch_422 ::
  T_Selective_240 ->
  () -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_branch_422 v0 v1 v2 v3 v4 v5 v6
  = coe du_branch_394 (coe v0) v4 v5 v6
-- FunctorApplicativeSelectiveMonad._.distr*>S
d_distr'42''62'S_424 ::
  T_Selective_240 ->
  () ->
  () ->
  MAlonzo.Code.Either.T__'8846'__10 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_distr'42''62'S_424 = erased
-- FunctorApplicativeSelectiveMonad._.idS
d_idS_426 ::
  T_Selective_240 ->
  () -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_idS_426 = erased
-- FunctorApplicativeSelectiveMonad._.select
d_select_428 ::
  T_Selective_240 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_select_428 v0 = coe d_select_316 (coe v0)
-- FunctorApplicativeSelectiveMonad.Monad
d_Monad_432 a0 = ()
data T_Monad_432
  = C_Monad'46'constructor_17881 T_Selective_240
                                 (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
-- FunctorApplicativeSelectiveMonad.Monad.selectiveM
d_selectiveM_476 :: T_Monad_432 -> T_Selective_240
d_selectiveM_476 v0
  = case coe v0 of
      C_Monad'46'constructor_17881 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- FunctorApplicativeSelectiveMonad.Monad.bind
d_bind_482 ::
  T_Monad_432 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_bind_482 v0
  = case coe v0 of
      C_Monad'46'constructor_17881 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- FunctorApplicativeSelectiveMonad.Monad.idlM
d_idlM_492 ::
  T_Monad_432 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_idlM_492 = erased
-- FunctorApplicativeSelectiveMonad.Monad.idrM
d_idrM_498 ::
  T_Monad_432 -> () -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_idrM_498 = erased
-- FunctorApplicativeSelectiveMonad.Monad.assocM
d_assocM_514 ::
  T_Monad_432 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Equality.T__'8801'__8
d_assocM_514 = erased
-- FunctorApplicativeSelectiveMonad.Monad._>>=_
d__'62''62''61'__520 ::
  (() -> ()) ->
  T_Monad_432 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__520 ~v0 v1 ~v2 ~v3 v4 v5
  = du__'62''62''61'__520 v1 v4 v5
du__'62''62''61'__520 ::
  T_Monad_432 -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'62''62''61'__520 v0 v1 v2
  = coe d_bind_482 v0 erased erased v1 v2
-- FunctorApplicativeSelectiveMonad.Monad.return
d_return_528 ::
  (() -> ()) -> T_Monad_432 -> () -> AgdaAny -> AgdaAny
d_return_528 ~v0 v1 ~v2 = du_return_528 v1
du_return_528 :: T_Monad_432 -> AgdaAny -> AgdaAny
du_return_528 v0
  = coe
      d_pure_148 (d_applicativeS_306 (coe d_selectiveM_476 (coe v0)))
      erased
-- FunctorApplicativeSelectiveMonad.Monad._>>_
d__'62''62'__534 ::
  (() -> ()) ->
  T_Monad_432 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__534 ~v0 v1 ~v2 ~v3 v4 v5 = du__'62''62'__534 v1 v4 v5
du__'62''62'__534 :: T_Monad_432 -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__534 v0 v1 v2
  = coe du__'62''62''61'__520 (coe v0) (coe v1) (coe (\ v3 -> v2))
-- FunctorApplicativeSelectiveMonad._._>>_
d__'62''62'__544 ::
  (() -> ()) ->
  T_Monad_432 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__544 ~v0 v1 = du__'62''62'__544 v1
du__'62''62'__544 ::
  T_Monad_432 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__544 v0 v1 v2 v3 v4
  = coe du__'62''62'__534 (coe v0) v3 v4
-- FunctorApplicativeSelectiveMonad._._>>=_
d__'62''62''61'__546 ::
  (() -> ()) ->
  T_Monad_432 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__546 ~v0 v1 = du__'62''62''61'__546 v1
du__'62''62''61'__546 ::
  T_Monad_432 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'62''62''61'__546 v0 v1 v2 v3 v4
  = coe du__'62''62''61'__520 (coe v0) v3 v4
-- FunctorApplicativeSelectiveMonad._.assocM
d_assocM_548 ::
  T_Monad_432 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Equality.T__'8801'__8
d_assocM_548 = erased
-- FunctorApplicativeSelectiveMonad._.bind
d_bind_550 ::
  T_Monad_432 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_bind_550 v0 = coe d_bind_482 (coe v0)
-- FunctorApplicativeSelectiveMonad._.idlM
d_idlM_552 ::
  T_Monad_432 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_idlM_552 = erased
-- FunctorApplicativeSelectiveMonad._.idrM
d_idrM_554 ::
  T_Monad_432 -> () -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_idrM_554 = erased
-- FunctorApplicativeSelectiveMonad._.return
d_return_556 ::
  (() -> ()) -> T_Monad_432 -> () -> AgdaAny -> AgdaAny
d_return_556 ~v0 v1 = du_return_556 v1
du_return_556 :: T_Monad_432 -> () -> AgdaAny -> AgdaAny
du_return_556 v0 v1 = coe du_return_528 (coe v0)
-- FunctorApplicativeSelectiveMonad._.selectiveM
d_selectiveM_558 :: T_Monad_432 -> T_Selective_240
d_selectiveM_558 v0 = coe d_selectiveM_476 (coe v0)
-- FunctorApplicativeSelectiveMonad.Alternative
d_Alternative_562 a0 = ()
data T_Alternative_562
  = C_Alternative'46'constructor_19215 T_Applicative_86
                                       (() -> AgdaAny) (() -> AgdaAny -> AgdaAny -> AgdaAny)
-- FunctorApplicativeSelectiveMonad.Alternative.applicativeF
d_applicativeF_598 :: T_Alternative_562 -> T_Applicative_86
d_applicativeF_598 v0
  = case coe v0 of
      C_Alternative'46'constructor_19215 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- FunctorApplicativeSelectiveMonad.Alternative.empty
d_empty_602 :: T_Alternative_562 -> () -> AgdaAny
d_empty_602 v0
  = case coe v0 of
      C_Alternative'46'constructor_19215 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- FunctorApplicativeSelectiveMonad.Alternative._<|>_
d__'60''124''62'__606 ::
  T_Alternative_562 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''124''62'__606 v0
  = case coe v0 of
      C_Alternative'46'constructor_19215 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- FunctorApplicativeSelectiveMonad.Alternative.idlAlt
d_idlAlt_612 ::
  T_Alternative_562 ->
  () -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_idlAlt_612 = erased
-- FunctorApplicativeSelectiveMonad.Alternative.idrAlt
d_idrAlt_618 ::
  T_Alternative_562 ->
  () -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_idrAlt_618 = erased
-- FunctorApplicativeSelectiveMonad.Alternative.assocAlt
d_assocAlt_628 ::
  T_Alternative_562 ->
  () ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_assocAlt_628 = erased
-- FunctorApplicativeSelectiveMonad._._<|>_
d__'60''124''62'__632 ::
  T_Alternative_562 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''124''62'__632 v0 = coe d__'60''124''62'__606 (coe v0)
-- FunctorApplicativeSelectiveMonad._.applicativeF
d_applicativeF_634 :: T_Alternative_562 -> T_Applicative_86
d_applicativeF_634 v0 = coe d_applicativeF_598 (coe v0)
-- FunctorApplicativeSelectiveMonad._.assocAlt
d_assocAlt_636 ::
  T_Alternative_562 ->
  () ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_assocAlt_636 = erased
-- FunctorApplicativeSelectiveMonad._.empty
d_empty_638 :: T_Alternative_562 -> () -> AgdaAny
d_empty_638 v0 = coe d_empty_602 (coe v0)
-- FunctorApplicativeSelectiveMonad._.idlAlt
d_idlAlt_640 ::
  T_Alternative_562 ->
  () -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_idlAlt_640 = erased
-- FunctorApplicativeSelectiveMonad._.idrAlt
d_idrAlt_642 ::
  T_Alternative_562 ->
  () -> AgdaAny -> MAlonzo.Code.Equality.T__'8801'__8
d_idrAlt_642 = erased
