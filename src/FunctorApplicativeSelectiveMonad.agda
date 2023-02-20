{-# OPTIONS --prop --rewriting #-}

{-
Made by: Viktor Bense, 2022. 03. 10.
-}

open import Prelude
open import Either
open import Equality

module FunctorApplicativeSelectiveMonad where

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    idF : {A : Set} → fmap {A} {A} id ≡ id
    ∘F : {A B C : Set}{f : B → C}{g : A → B} → (fmap f ∘ fmap g) ≡ fmap (f ∘ g)
  
  _<$>_ : {A B : Set} → (A → B) → F A → F B
  f <$> x = fmap f x

  _<$_ : {A B : Set} → A → F B → F A
  x <$ y = fmap (const x) y

  infixl 4 _<$>_
  infixl 4 _<$_

open Functor {{...}} public

record Applicative (F : Set → Set) : Set₁ where
  field
    overlap {{functorF}} : Functor F
    pure : {A : Set} → A → F A
    _⊛_ : {A B : Set} → F (A → B) → F A → F B
    idA : {A : Set}{x : F A} → (pure id ⊛ x) ≡ x
    ∘A : {A B C : Set}{a : F (B → C)}{b : F (A → B)}{c : F A} → (pure _∘_ ⊛ a ⊛ b ⊛ c) ≡ (a ⊛ (b ⊛ c))
    homoA : {A B : Set}{f : A → B}{x : A} → (pure f ⊛ pure x) ≡ pure (f x)
    interchangeA : {A B : Set}{f : F (A → B)}{x : A} → (f ⊛ pure x) ≡ (pure (λ g → g x) ⊛ f)
  infixl 4 _⊛_
  
  _*>_ : {A B : Set} → F A → F B → F B
  x *> y = id <$ x ⊛ y
  
  _<*_ : {A B : Set} → F A → F B → F A
  x <* y = const <$> x ⊛ y

  infixl 4 _<*_
  infixl 4 _*>_

open Applicative {{...}} public

record Selective (S : Set → Set) : Set₁ where
  field
    overlap {{applicativeS}} : Applicative S
    select : {A B : Set}(ab : S (A ⊎ B))(f : S (A → B)) → S B
    idS : {A : Set}{x : S (A ⊎ A)} → select x (pure id) ≡ fmap (λ y → case y id id) x
    distr*>S : {A B : Set}{x : A ⊎ B}{y z : S (A → B)} → select (pure x) (y *> z) ≡ (select (pure x) y *> select (pure x) z)
    assocS : {A B C : Set}{x : S (A ⊎ B)}{y : S (C ⊎ (A → B))}{z : S (C → A → B)} → (select x (select y z)) ≡ (select (select (fmap (λ a → case a ι₁ λ b → ι₂ (ι₂ b)) x) (fmap (λ c a → case c (λ c₁ → ι₁ (c₁ ,Σ a)) λ f → ι₂ (f a)) y)) (fmap (λ f c → f (π₁ c) (π₂ c)) z))

  _<*?_ : {A B : Set}(ab : S (A ⊎ B))(f : S (A → B)) → S B
  _<*?_ {A} {B} ab f = select {A} {B} ab f
  infixl 4 _<*?_
  
  branch : {A B C : Set}(ab : S (A ⊎ B)) → S (A → C) → S (B → C) → S C
  branch {A} {B} {C} ab f g = select {B} {C} (select {A} {B ⊎ C} (fmap {S} {A ⊎ B} (λ ab → case ab ι₁ (ι₂ ∘ ι₁)) ab) (fmap {S} {A → C} (λ ac a → ι₂ (ac a)) f)) g

open Selective {{...}} public

record Monad (M : Set → Set) : Set₁ where
  field
    overlap {{selectiveM}} : Selective M
    bind : {A B : Set} → M A → (A → M B) → M B
    idlM : {A B : Set}{f : A → M B}{x : A} → (bind (pure x) f) ≡ f x
    idrM : {A : Set}{x : M A} → (bind x pure) ≡ x
    assocM : {A B C : Set}{f : M A}{g : A → M B}{h : B → M C} → (bind (bind f g) h) ≡ (bind f (λ x → bind (g x) h))
  
  _>>=_ : {A B : Set} → M A → (A → M B) → M B
  _>>=_ f x = bind f x
  infixl 1 _>>=_
  
  return : {A : Set} → A → M A
  return = pure

  _>>_ : {A B : Set} → M A → M B → M B
  x >> y = x >>= λ _ → y

  _>=>_ : {A B C : Set} → (A → M B) → (B → M C) → (A → M C)
  _>=>_ f g a = f a >>= g
  infixl 1 _>=>_

  -- asszociativitás szabály a fish operátorból triviálisabban látszik
  -- assocFish : (f >=> g) >=> h ≡ f >=> (g >=> h)
  -- ez ugyanazt írja le, mint az assocM szabály.

open Monad {{...}} public

record Alternative (F : Set → Set) : Set₁ where
  field
    overlap {{applicativeF}} : Applicative F
    empty : {A : Set} → F A
    _<|>_ : {A : Set} → F A → F A → F A
    idlAlt : {A : Set}{x : F A} → empty <|> x ≡ x
    idrAlt : {A : Set}{x : F A} → x <|> empty ≡ x
    assocAlt : {A : Set}{x y z : F A} → (x <|> y) <|> z ≡ x <|> (y <|> z)
  infixl 3 _<|>_

open Alternative {{...}} public