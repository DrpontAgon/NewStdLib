{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import FunctorApplicativeSelectiveMonad

module SkipList where

data SkipList (A : Set) : Set where
  [] : SkipList A
  Skip : SkipList A → SkipList A
  _::_ : A → SkipList A → SkipList A

infixr 5 _::_
infixr 5 _++_

_++_ : {A : Set} → SkipList A → SkipList A → SkipList A
[] ++ ys = ys
(Skip xs) ++ ys = Skip (xs ++ ys)
(x :: xs) ++ ys = x :: xs ++ ys

postulate
  funExt : ∀{i j} {A : Set i} {B : A → Set j} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

happly : ∀{i j} {A : Set i} {B : A → Set j} {f g : (x : A) → B x} (x : A) → f ≡ g → f x ≡ g x
happly x refl = refl

substp : ∀{i j}{A : Set i}(B : A → Prop j){a a' : A} → a ≡ a' → B a → B a'
substp B refl u = u

sym : ∀{i}{A : Set i}{a a' : A} → a ≡ a' → a' ≡ a
sym refl = refl

trans : ∀{i}{A : Set i}{a a' a'' : A} → a ≡ a' → a' ≡ a'' → a ≡ a''
trans refl refl = refl

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

_∎ : ∀{ℓ}{A : Set ℓ}(x : A) → x ≡ x
x ∎ = refl {x = x}

_≡⟨_⟩_ : ∀{ℓ}{A : Set ℓ}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

infix  3 _∎
infixr 2 _≡⟨_⟩_

idr[]++ : {A : Set}{xs : SkipList A} → xs ++ [] ≡ xs
idr[]++ {A} {[]} = refl
idr[]++ {A} {Skip xs} = cong Skip idr[]++
idr[]++ {A} {x :: xs} = cong (x ::_) (idr[]++ {A} {xs})

assoc++ : {A : Set}{a b c : SkipList A} → (a ++ b) ++ c ≡ a ++ b ++ c
assoc++ {A} {[]} {b} {c} = refl
assoc++ {A} {Skip xs} {b} {c} = cong Skip (assoc++ {A} {xs})
assoc++ {A} {a :: ax} {b} {c} = cong (a ::_) (assoc++ {A} {ax})

FunctorSkipList : Functor SkipList
FunctorSkipList = record
  { fmap = skipmap
  ; idF = idF'
  ; ∘F = compF } where
    skipmap : {A B : Set} → (A → B) → SkipList A → SkipList B
    skipmap f [] = []
    skipmap f (Skip xs) = Skip (skipmap f xs)
    skipmap f (x :: xs) = f x :: skipmap f xs

    funExtidF : {A : Set} → (xs : SkipList A) → skipmap id xs ≡ xs
    funExtidF {A} [] = refl
    funExtidF {A} (Skip xs) = cong Skip (funExtidF {A} xs)
    funExtidF {A} (x :: xs) = cong (x ::_) (funExtidF {A} xs)

    idF' : {A : Set} → skipmap {A} {A} id ≡ id
    idF' {A} = funExt funExtidF

    compF2 : {A B C : Set}{f : B → C}{g : A → B}(xs : SkipList A) → (skipmap f ∘ skipmap g) xs ≡ skipmap (f ∘ g) xs
    compF2 [] = refl
    compF2 (Skip xs) = cong Skip (compF2 xs)
    compF2 {f = f} {g = g} (x :: xs) = cong (f (g x) ::_) (compF2 xs)

    compF : {A B C : Set}{f : B → C}{g : A → B} → skipmap f ∘ skipmap g ≡ skipmap (f ∘ g)
    compF {f = f} {g = g} = funExt λ {[] → refl
                                    ; (Skip xs) → cong Skip (compF2 xs)
                                    ; (x :: xs) → cong (f (g x) ::_ ) (compF2 xs)}

ApplicativeSkipList : Applicative SkipList
ApplicativeSkipList = record
  { functorF = FunctorSkipList
  ; pure = _:: []
  ; _⊛_ = skipap
  ; idA = idA1
  ; ∘A = {!   !}
  ; homoA = refl
  ; interchangeA = λ {A} {B} {f} {x} → skipap f (x :: [])
      ≡⟨ apFmap1 ⟩
    fmap {{FunctorSkipList}} (λ z → z x) f
      ≡⟨ sym idr[]++ ⟩
    fmap {{FunctorSkipList}} (λ z → z x) f ++ []
    ∎ } where
    skipap : {A B : Set} → SkipList (A → B) → SkipList A → SkipList B
    skipap [] _ = []
    skipap (Skip fs) xs = Skip (skipap fs xs)
    skipap (f :: fs) xs = fmap {{FunctorSkipList}} f xs ++ skipap fs xs

    idA1 : {A : Set}{xs : SkipList A} → skipap (id :: []) xs ≡ xs
    idA1 {A} {[]} = refl
    idA1 {A} {Skip xs} = cong Skip (idA1 {A} {xs})
    idA1 {A} {x :: xs} = cong (x ::_) (idA1 {A} {xs})

    apFmap1 : {A B : Set}{x : A}{fs : SkipList (A → B)} → skipap fs (x :: []) ≡ fmap {{FunctorSkipList}} (λ g → g x) fs
    apFmap1 {A} {B} {x} {[]} = refl
    apFmap1 {A} {B} {x} {Skip fs} = cong Skip apFmap1
    apFmap1 {A} {B} {x} {f :: fs} = cong (f x ::_) apFmap1