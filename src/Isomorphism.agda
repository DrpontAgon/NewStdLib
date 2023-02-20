{-# OPTIONS --prop --rewriting #-}

module Isomorphism where

open import Prelude
open import Equality
open import Transitive
open import Reflexive
open import Symmetric
open import EquivalenceRelation

-- Equivalence realtion
infix 0 _≅_
record _≅_ {i} (A : Set i) (B : Set i) : Set (lsuc i) where
  field
    left→right : A → B
    right→left : B → A
    →∘←≡id : left→right ∘ right→left ≡ₛ id
    ←∘→≡id : right→left ∘ left→right ≡ₛ id

open _≅_ public

isoRefl : ∀{i} → {A : Set i} → A ≅ A
isoRefl = record 
  { left→right = λ z → z
  ; right→left = λ z → z
  ; →∘←≡id = reflₛ
  ; ←∘→≡id = reflₛ }

instance
  ≅Refl : ∀{i} → Reflexive {lsuc i} {_} _≅_
  ≅Refl = record { reflexive = isoRefl }

isoSym : ∀{i} → {A B : Set i} → A ≅ B → B ≅ A
isoSym record { left→right = left→right ; right→left = right→left ; →∘←≡id = →∘←≡id ; ←∘→≡id = ←∘→≡id } = record 
  { left→right = right→left
  ; right→left = left→right
  ; →∘←≡id = ←∘→≡id
  ; ←∘→≡id = →∘←≡id }

instance
  ≅Sym : ∀{i} → Symmetric {lsuc i} {_} _≅_
  ≅Sym = record { sym = isoSym }

isoTrans : ∀{i} → {A B C : Set i} → A ≅ B → B ≅ C → A ≅ C
isoTrans {i} {A} {B} {C} record { left→right = f₁ ; right→left = g₁ ; →∘←≡id = →∘←≡id₁ ; ←∘→≡id = ←∘→≡id₁ }
         record { left→right = left→right ; right→left = right→left ; →∘←≡id = →∘←≡id ; ←∘→≡id = ←∘→≡id } = record 
  { left→right = λ z → left→right (f₁ z) ; right→left = λ z → g₁ (right→left z)
  ; →∘←≡id = funExtₛ λ x → fgid {x}
  ; ←∘→≡id = funExtₛ (λ x → gfid {x}) } where
    fgid : {x : C} → left→right (f₁ (g₁ (right→left x))) ≡ₛ x
    fgid {x} = 
      left→right (f₁ (g₁ (right→left x))) 
      ≡⟨ congₛ (λ y → left→right (y (right→left x))) →∘←≡id₁ ⟩ₛ 
      left→right (id (right→left x))
      ≡⟨ reflₛ ⟩ₛ 
      left→right (right→left x)
      ≡⟨ happlyₛ →∘←≡id x ⟩ₛ 
      id x
      ≡⟨ reflₛ ⟩ₛ 
      x
      ∎ₛ

    gfid : {x : A} → g₁ (right→left (left→right (f₁ x))) ≡ₛ x
    gfid {x} = 
      g₁ (right→left (left→right (f₁ x)))
      ≡⟨ congₛ (λ y → g₁ (y (f₁ x))) ←∘→≡id ⟩ₛ
      g₁ (f₁ x)
      ≡⟨ happlyₛ ←∘→≡id₁ x ⟩ₛ
      x
      ∎ₛ

instance
  ≅Trans : ∀{i} → Transitive {lsuc i} {_} _≅_
  ≅Trans = record { trans = isoTrans }

instance
  ≅EqRel : ∀{i} → EquivalenceRelation {lsuc i} {_} _≅_
  ≅EqRel = record {}
{-
instance
  ℕ≅ℤ : ℕ ≅ ℤ
  ℕ≅ℤ = record 
    { left→right = {!   !}
    ; right→left = {!   !}
    ; →∘←≡id = {!   !}
    ; ←∘→≡id = {!   !} } where
      f'' : ℕ → ℕ → ℤ
      f'' helper zero = pos helper
      f'' helper (suc zero) = negsuc helper
      f'' helper (suc (suc n)) = f'' (suc helper) n
      
      f' : ℕ → ℤ
      f' = f'' 0

      g' : ℤ → ℕ
      g' (pos zero) = 0
      g' (pos (suc zero)) = 2
      g' (pos (suc (suc x))) = suc (suc (g' (pos x)))
      g' (negsuc zero) = 1
      g' (negsuc (suc zero)) = 3
      g' (negsuc (suc (suc x))) = suc (suc (g' (negsuc x)))

      gf1 : {x y : ℕ} → g' (f'' y x) ≡ₛ 2 * y + x
      gf1 {zero} {zero} = reflₛ
      gf1 {suc x} {zero} = {!   !}
      gf1 {zero} {suc y} = {!   !}
      gf1 {suc x} {suc y} = {!   !}

      fright→left : {x : ℤ} → (f' ∘ g') x ≡ₛ x
      fright→left {pos zero} = reflₛ
      fright→left {pos (suc zero)} = reflₛ
      fright→left {pos (suc (suc x))} = {!   !}
      fright→left {negsuc x} = {!   !}

      gleft→right : {x : ℕ} → (g' ∘ f') x ≡ₛ x
      gleft→right {zero} = reflₛ
      gleft→right {suc zero} = reflₛ
      gleft→right {suc (suc x)} = {!   !}

-}
{-
instance
  Maybe≅Either⊤ : {A : Set} → Maybe A ≅ ⊤ ⊎ A
  Maybe≅Either⊤ {A} = record 
    { left→right = f'
    ; right→left = g'
    ; →∘←≡id = funExtₛ (λ x → fgid {x})
    ; ←∘→≡id = funExtₛ (λ x → gfid {x}) } where
    
      f' : Maybe A → ⊤ ⊎ A
      f' nothinright→left = ι₁ trivial
      f' (just x) = ι₂ x

      g' : ⊤ ⊎ A → Maybe A
      g' (ι₁ trivial) = nothing
      g' (ι₂ x) = just x

      fgid : ∀{x} → f' (g' x) ≡ₛ x
      fgid {ι₁ trivial} = reflₛ
      fgid {ι₂ x} = reflₛ

      gfid : ∀{x} → g' (f' x) ≡ₛ x
      gfid {nothing} = reflₛ
      gfid {just x} = reflₛ

-- Prove that (List ⊤) is isomorphic to ℕ
instance
  List⊤≅ℕ : List ⊤ ≅ ℕ
  List⊤≅ℕ = record 
    { left→right = f'
    ; right→left = g'
    ; →∘←≡id = funExtₛ fgid
    ; ←∘→≡id = funExtₛ gfid } where
      f' : List ⊤ → ℕ
      f' []        = 0
      f' (x :: xs) = suc (f' xs)

      g' : ℕ → List ⊤
      g' 0       = []
      g' (suc n) = trivial :: g' n

      fgid : ∀(x) → f' (g' x) ≡ₛ x
      fgid zero    = reflₛ 
      fgid (suc x) = congₛ suc (fgid x) 

      gfid : ∀(x) → g' (f' x) ≡ₛ x
      gfid []        = reflₛ
      gfid (x :: xs) = congₛ (x ::_) (gfid xs)

-- Prove that ⊤ is isomorphic to ⊥ → A
instance
  ⊤≅A : {A : Set} → ⊤ ≅ (⊥ → A)
  ⊤≅A {A} = record 
    { left→right = f'
    ; right→left = g'
    ; →∘←≡id = funExtₛ fgid
    ; ←∘→≡id = funExtₛ gfid } where
      f' : ⊤ → ⊥ → A
      f' _ ()

      g' : (⊥ → A) → ⊤
      g' _ = trivial

      fgid : ∀(x) → f' (g' x) ≡ₛ x
      fgid x = funExtₛ λ {()}

      gfid : ∀(x) → g' (f' x) ≡ₛ x
      gfid trivial = reflₛ

-}