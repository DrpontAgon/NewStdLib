{-# OPTIONS --prop --rewriting #-}

open import Prelude.Set
-- open import Transitive
-- open import Fin
open import Natural
open import Equality.Set.Base
open import Equality.Set.Relations
open import Relation.Symmetric.Set
-- open import Bool
-- open import FunctorApplicativeSelectiveMonad
-- open import Equality
-- open import Symmetric

module Vector where

infixr 5 _∷_
infixr 5 _++_

data Vector {i} (A : Set i) : ℕ → Set i where
  []   : Vector A 0 
  _∷_  : {n : ℕ} → A → Vector A n → Vector A (suc n)

head : ∀{i}{A : Set i} → {n : ℕ} → Vector A (suc n) → A
head (x ∷ _) = x

tail : ∀{i}{A : Set i} → {n : ℕ} → Vector A (suc n) → Vector A n
tail (_ ∷ xs) = xs

init : ∀{i}{A : Set i} → {n : ℕ} → Vector A (suc n) → Vector A n
init {n = 0}     (x ∷ []) = []
init {n = suc _} (x ∷ ys) = x ∷ init ys

last : ∀{i}{A : Set i} → {n : ℕ} → Vector A (suc n) → A
last {n = zero} (x ∷ []) = x
last {n = suc n} (_ ∷ xs) = last xs

_++_ : ∀{i}{A : Set i}{n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
[]       ++ y = y
(x ∷ xs) ++ y = x ∷ xs ++ y

{-
_!!_ : ∀{i}{A : Set i} → {n : ℕ} → Vector A (suc n) → Fin {i} (suc n) → A
(x ∷ xs) !! zero  = x
(x ∷ y ∷ xs) !! (suc i) = (y :: xs) !! i
-}
replicate : ∀{i}{A : Set i}(n : ℕ) → A → Vector A n
replicate zero a = []
replicate (suc n) a = a ∷ replicate n a

reverse : ∀{i}{A : Set i} → {n : ℕ} → Vector A n → Vector A n
reverse = reverseAcc [] where
  reverseAcc : ∀{j}{B : Set j}{k m} → Vector B k → Vector B m → Vector B (k + m)
  reverseAcc {B = B} {k} {0} acc [] = subst (Vector B) (idr+ ⁻¹) acc
  reverseAcc {B = B} {k} {(suc m)} acc (x ∷ xs) = subst (Vector B) (sucr+ ⁻¹) (reverseAcc (x ∷ acc) xs)
{-
intersperse : ∀{i}{A : Set i} → {n : ℕ} → A → Vector A n → Vector A (n + n - 1)
intersperse {i} {A} {zero} e [] = []
intersperse {i} {A} {suc zero} e (x :: []) = x :: []
intersperse {i} {A} {suc (suc n)} e (x :: y :: xs) = x :: substₛ (Vector A) pr (e :: intersperse {i} {A} {suc n} e (y :: xs)) where
  pr : suc (suc n + suc n - 1) ≡ₛ n + suc (suc n)
  pr = 
    suc (n + suc n) 
    ≡⟨ sym (sucr+ {n}) ⟩ₛ 
    n + suc (suc n)
    ∎ₛ

take : ∀{i}{A : Set i} → {n : ℕ} → (a : ℕ) → Vector A n → Vector A (min n a)
take {i} {A} {.0} _ [] = []
take {i} {A} {.(suc _)} zero (x :: xs) = []
take {i} {A} {suc n} (suc a) (x :: xs) = x :: take a xs

drop : ∀{i}{A : Set i} → {n : ℕ} → (a : ℕ) → Vector A n → Vector A (n - min n a)
drop {i} {A} {.0} a [] = []
drop {i} {A} {suc n} zero (x :: xs) = x :: xs
drop {i} {A} {suc n} (suc a) (x :: xs) = drop {i} {A} {n} a xs

count : ∀{i}{A : Set i} → {n : ℕ} → (A → 𝟚) → Vector A n → ∃ x ∈ ℕ ∣ x ≤ n
count {i} {A} {0} f [] = zero ,Σ le
count {i} {A} {suc n} f (x :: xs) = let (k ,Σ pr) = count {i} {A} {n} f xs in if f x then suc k ,Σ leSuc pr else (k ,Σ trans pr suc≤)

filter : ∀{i}{A : Set i} → {n : ℕ} → (p : A → 𝟚) → (xs : Vector A n) → Vector A (π₁ (count p xs))
filter p [] = []
filter p (x :: xs) with p x
... | true = x :: filter p xs
... | false = filter p xs

instance
  FunctorVector : {n : ℕ} → Functor (λ A → Vector A n)
  FunctorVector = record 
    { fmap = map
    ; idF = mapId
    ; ∘F = funExt compF } where
      map : {A B : Set}{n : ℕ}(f : A → B) → Vector A n → Vector B n
      map f [] = []
      map f (x :: xs) = f x :: map f xs

      mapId : {A : Set}{n : ℕ} → map {A} {A} {n} id ≡ id
      mapId = funExt λ {[] → refl
                      ; (x :: xs) → cong (x ::_) (happly mapId xs)}

      compF : {A B C : Set}{n : ℕ}{f : B → C}{g : A → B}(x : Vector A n)
        → (map f ∘ map g) x ≡ map (f ∘ g) x
      compF {A} {B} {C} {.0} {f} {g} [] = refl
      compF {A} {B} {C} {.(suc _)} {f} {g} (x :: xs) = cong (f (g x) ::_) (compF xs)
-}      