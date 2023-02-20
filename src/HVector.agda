{-# OPTIONS --prop --rewriting #-}

module HVector where

open import Vector using (Vector ; [] ; _::_ ; VNil ; VCons)
import Vector as V
open import Natural
open import Fin
open import Agda.Primitive

infixr 5 _::_
infixr 5 _++_

data HVector {i : Level} : (n : ℕ) → (xs : Vector (Set i) n) → Set i where
  HNil : HVector 0 []
  HCons : {n : ℕ}{x : Set i}{xs : Vector (Set i) n} → x → HVector {i} n xs → HVector {i} (suc n) (x :: xs)

pattern [] = HNil
pattern _::_ x xs = HCons x xs

head : ∀{i}{n : ℕ}{xs : Vector (Set i) (suc n)} → HVector {i} (suc n) xs → V.head xs
head (x :: _) = x

tail : ∀{i}{n : ℕ}{xs : Vector (Set i) (suc n)} → HVector {i} (suc n) xs → HVector {i} n (V.tail xs)
tail (_ :: xs) = xs

last : ∀{i}{n : ℕ}{xs : Vector (Set i) (suc n)} → HVector {i} (suc n) xs → V.last xs
last (x :: [])         = x
last (x :: v@(_ :: _)) = last v

init : ∀{i}{n : ℕ}{xs : Vector (Set i) (suc n)} → HVector {i} (suc n) xs → HVector {i} n (V.init xs)
init (x :: [])         = []
init (x :: v@(_ :: _)) = x :: init v

_++_ : ∀{i}{n m : ℕ}{xs : Vector (Set i) n}{ys : Vector (Set i) m} → HVector n xs → HVector m ys → HVector (n + m) (xs V.++ ys)
HNil      ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

_!!_ : ∀{i}{n : ℕ}{xs : Vector (Set i) (suc n)} → HVector (suc n) xs → (k : Fin (suc n)) → xs V.!! k
(x :: v)          !! zero  = x
(x :: v@(_ :: _)) !! suc k = v !! k

replicate : ∀{i}{A : Set i}(n : ℕ)(a : A) → HVector n (V.replicate n A)
replicate zero    a = []
replicate (suc n) a = a :: replicate n a

take : ∀{i}{n : ℕ}{xs : Vector (Set i) n} → (k : ℕ) → HVector {i} n xs → HVector {i} (min n k) (V.take k xs)
take k [] = []
take zero (x :: v) = []
take (suc k) (x :: v) = x :: take k v

drop : ∀{i}{n : ℕ}{xs : Vector (Set i) n} → (k : ℕ) → HVector {i} n xs → HVector {i} (n - min n k) (V.drop k xs)
drop k [] = []
drop zero (x :: v) = x :: v
drop (suc k) (x :: v) = drop k v
