{-# OPTIONS --prop --rewriting #-}

{-
Made by: Viktor Bense, 2022. 04. 11.
-}

module Maybe where

open import Prelude public
open import Either public
open import FunctorApplicativeSelectiveMonad public

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

syntax Maybe A = A ??
syntax nothing = ∅
syntax just x = x !

fromMaybe : {A B : Set} → (A → B → B) → B → A ?? → B
fromMaybe f x ∅ = x
fromMaybe f x (y !) = f y x

instance
  FunctorMaybe : Functor Maybe
  FunctorMaybe = record 
    { fmap = maybeMap
    ; idF = idMaybe
    ; ∘F = ∘Maybe
    } where
  
    maybeMap : {A B : Set} → (A → B) → Maybe A → Maybe B
    maybeMap f nothing = nothing
    maybeMap f (just x) = just (f x)

    idMaybe2 : {A : Set}(x : Maybe A) → maybeMap {A} {A} id x ≡ id x
    idMaybe2 {A} nothing = refl
    idMaybe2 {A} (just x) = refl

    idMaybe : {A : Set} → maybeMap {A} {A} id ≡ id
    idMaybe = funExt idMaybe2

    ext∘Maybe : {A B C : Set}{f : B → C}{g : A → B}(x : Maybe A) → (maybeMap f ∘ maybeMap g) x ≡ maybeMap (f ∘ g) x
    ext∘Maybe nothing = refl
    ext∘Maybe (just x) = refl

    ∘Maybe : {A B C : Set}{f : B → C}{g : A → B} → (maybeMap f ∘ maybeMap g) ≡ maybeMap (f ∘ g)
    ∘Maybe = funExt ext∘Maybe

instance
  ApplicativeMaybe : Applicative Maybe
  ApplicativeMaybe = record
    { functorF = FunctorMaybe
    ; pure = just
    ; _⊛_ = apMaybe
    ; idA = idAMaybe
    ; ∘A = ∘AMaybe
    ; homoA = refl
    ; interchangeA = interchangeAMaybe
    } where

    apMaybe : {A B : Set} → Maybe (A → B) → Maybe A → Maybe B
    apMaybe (just f) (just x) = just (f x)
    apMaybe (just _) nothing  = nothing
    apMaybe nothing  _        = nothing

    idAMaybe : {A : Set}{x : Maybe A} → apMaybe (just id) x ≡ x
    idAMaybe {A} {nothing} = refl
    idAMaybe {A} {just x} = refl

    ∘AMaybe : {A B C : Set}{a : Maybe (B → C)}{b : Maybe (A → B)}{c : Maybe A}
            → apMaybe (apMaybe (apMaybe (just _∘_) a) b) c ≡ apMaybe a (apMaybe b c)
    ∘AMaybe {a = nothing} {b = nothing} {c = nothing} = refl
    ∘AMaybe {a = nothing} {b = nothing} {c = just x} = refl
    ∘AMaybe {a = nothing} {b = just x} {c = nothing} = refl
    ∘AMaybe {a = nothing} {b = just x} {c = just x₁} = refl
    ∘AMaybe {a = just x} {b = nothing} {c = nothing} = refl
    ∘AMaybe {a = just x} {b = nothing} {c = just x₁} = refl
    ∘AMaybe {a = just x} {b = just x₁} {c = nothing} = refl
    ∘AMaybe {a = just x} {b = just x₁} {c = just x₂} = refl

    interchangeAMaybe : {A B : Set} {f : Maybe (A → B)} {x : A}
                      → apMaybe f (just x) ≡ apMaybe (just (λ g → g x)) f
    interchangeAMaybe {f = nothing} = refl
    interchangeAMaybe {f = just x} = refl

instance 
  SelectiveMaybe : Selective Maybe
  SelectiveMaybe = record
    { applicativeS = ApplicativeMaybe
    ; select = selectMaybe
    ; idS = idSMaybe
    ; distr*>S = distr*>SMaybe
    ; assocS = assocSMaybe
    } where
  
    selectMaybe : {A B : Set} → Maybe (A ⊎ B) → Maybe (A → B) → Maybe B
    selectMaybe nothing       f        = nothing
    selectMaybe (just (ι₁ x)) nothing  = nothing
    selectMaybe (just (ι₁ x)) (just f) = just (f x)
    selectMaybe (just (ι₂ x)) _        = just x
  
    idSMaybe : {A : Set}{x : Maybe (A ⊎ A)} → selectMaybe x (just id) ≡ fmap (λ y → case y id id) x
    idSMaybe {x = nothing} = refl
    idSMaybe {x = just (ι₁ x)} = refl
    idSMaybe {x = just (ι₂ x)} = refl
  
    distr*>SMaybe : {A B : Set}{x : A ⊎ B}{y z : Maybe (A → B)} 
                  → selectMaybe (just x) (y *> z) ≡ (selectMaybe (just x) y *> selectMaybe (just x) z)
    distr*>SMaybe {x = ι₁ x} {y = nothing} {z = nothing} = refl
    distr*>SMaybe {x = ι₁ x} {y = nothing} {z = just x₁} = refl
    distr*>SMaybe {x = ι₁ x} {y = just x₁} {z = nothing} = refl
    distr*>SMaybe {x = ι₁ x} {y = just x₁} {z = just x₂} = refl
    distr*>SMaybe {x = ι₂ x} {y = y} {z = z} = refl

    assocSMaybe : {A B C : Set} {x : Maybe (A ⊎ B)} {y : Maybe (C ⊎ (A → B))}
      {z : Maybe (C → A → B)} → selectMaybe x (selectMaybe y z) ≡ selectMaybe (selectMaybe (fmap (λ a → case a ι₁ (λ b → ι₂ (ι₂ b))) x) (fmap (λ c a → case c (λ c₁ → ι₁ (c₁ ,Σ a)) (λ f → ι₂ (f a))) y)) (fmap (λ f c → f (π₁ c) (π₂ c)) z)
    assocSMaybe {x = nothing} {y = y} {z = z} = refl
    assocSMaybe {x = just (ι₁ x)} {y = nothing} {z = z} = refl
    assocSMaybe {x = just (ι₁ x)} {y = just (ι₁ x₁)} {z = nothing} = refl
    assocSMaybe {x = just (ι₁ x)} {y = just (ι₂ x₁)} {z = nothing} = refl
    assocSMaybe {x = just (ι₁ x)} {y = just (ι₁ x₁)} {z = just z} = refl
    assocSMaybe {x = just (ι₁ x)} {y = just (ι₂ x₁)} {z = just z} = refl
    assocSMaybe {x = just (ι₂ x)} {y = y} {z = z} = refl

instance
  MonadMaybe : Monad Maybe
  MonadMaybe = record
    { bind = bindMaybe
    ; idlM = refl
    ; idrM = idrMMaybe
    ; assocM = λ {A} {B} {C} {f} → assocMMaybe {A} {B} {C} {f}
    } where

    bindMaybe : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
    bindMaybe nothing f  = nothing
    bindMaybe (just x) f = f x

    idrMMaybe : {A : Set} {x : Maybe A} → bindMaybe x just ≡ x
    idrMMaybe {x = nothing} = refl
    idrMMaybe {x = just x} = refl

    assocMMaybe : {A B C : Set} {f : Maybe A} {g : A → Maybe B} {h : B → Maybe C}
                → bindMaybe (bindMaybe f g) h ≡ bindMaybe f (λ x → bindMaybe (g x) h)
    assocMMaybe {f = nothing} = refl
    assocMMaybe {f = just x} = refl

instance
  AlternativeMaybe : Alternative Maybe
  AlternativeMaybe = record
    { empty = nothing
    ; _<|>_ = alt
    ; idlAlt = refl
    ; idrAlt = idrAlt'
    ; assocAlt = λ {A} {x} → assocAlt' {x = x}
    } where
    
    alt : {A : Set} → Maybe A → Maybe A → Maybe A
    alt nothing y = y
    alt (just x) y = just x

    idrAlt' : {A : Set} {x : Maybe A} → alt x nothing ≡ x
    idrAlt' {x = nothing} = refl
    idrAlt' {x = just x} = refl

    assocAlt' : {A : Set} {x y z : Maybe A} → alt (alt x y) z ≡ alt x (alt y z)
    assocAlt' {A} {nothing} {y} {z} = refl
    assocAlt' {A} {just x} {y} {z} = refl