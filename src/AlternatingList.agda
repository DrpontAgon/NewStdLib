{-# OPTIONS --prop --rewriting #-}

module AlternatingList where

open import Prelude
open import FunctorApplicativeSelectiveMonad

data AlternatingList (A : Set) (B : Set) : Set where
  Nil : AlternatingList A B
  Cons : A → AlternatingList B A → AlternatingList A B

FunctorAlternatingList : {A : Set} → Functor (AlternatingList A)
FunctorAlternatingList {A} = record
  { fmap = altMap 
  ; idF = funExt idAlt 
  ; ∘F = funExt ∘Alt } where
    altMap : {B C : Set} → (B → C) → AlternatingList A B → AlternatingList A C
    altMap f Nil = Nil
    altMap f (Cons x Nil) = Cons x Nil
    altMap f (Cons x (Cons y xs)) = Cons x (Cons (f y) (altMap f xs))

    idAlt : {B : Set} → (x : AlternatingList A B) → altMap id x ≡ x
    idAlt Nil = refl
    idAlt (Cons x Nil) = refl
    idAlt (Cons x (Cons y xs)) = cong (λ z → Cons x (Cons y z)) (idAlt xs)

    ∘Alt : {D B C : Set} {f : B → C} {g : D → B} 
        → (x : AlternatingList A D) → (altMap f ∘ altMap g) x ≡ altMap (f ∘ g) x
    ∘Alt Nil = refl
    ∘Alt (Cons x Nil) = refl
    ∘Alt {f = f} {g = g} (Cons x (Cons y xs)) = cong (λ z → Cons x (Cons (f (g y)) z)) (∘Alt xs)

FunctorAlternatingList2 : {B : Set} → Functor (λ x → AlternatingList x B)
FunctorAlternatingList2 {B} = record
  { fmap = altMap
  ; idF = funExt idAlt
  ; ∘F = funExt ∘Alt } where
    altMap : {A C : Set} → (A → C) → AlternatingList A B → AlternatingList C B
    altMap f Nil = Nil
    altMap f (Cons x Nil) = Cons (f x) Nil
    altMap f (Cons x (Cons y xs)) = Cons (f x) (Cons y (altMap f xs))

    idAlt : {A : Set} → (x : AlternatingList A B) → altMap id x ≡ x
    idAlt Nil = refl
    idAlt (Cons x Nil) = refl
    idAlt (Cons x (Cons y xs)) = cong (λ z → Cons x (Cons y z)) (idAlt xs)

    ∘Alt : {D A C : Set} {f : A → C} {g : D → A} 
        → (x : AlternatingList D B) → (altMap f ∘ altMap g) x ≡ altMap (f ∘ g) x
    ∘Alt Nil = refl
    ∘Alt (Cons x Nil) = refl
    ∘Alt {f = f} {g = g} (Cons x (Cons y xs)) = cong (λ z → Cons (f (g x)) (Cons y z)) (∘Alt xs)