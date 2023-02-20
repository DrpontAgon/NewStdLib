{-# OPTIONS --without-K --safe #-}

module Bool.Set where

open import Agda.Builtin.Bool
  renaming (Bool to 𝟚)

infixr 6 _∧_
infixr 5 _∨_ _xor_

not : 𝟚 → 𝟚
not true  = false
not false = true

_∧_ : 𝟚 → 𝟚 → 𝟚
true  ∧ b = b
false ∧ b = false

_∨_ : 𝟚 → 𝟚 → 𝟚
true  ∨ b = true
false ∨ b = b

_xor_ : 𝟚 → 𝟚 → 𝟚
true  xor b = not b
false xor b = b

infixr 4.9 _⊃_

_⊃_ : 𝟚 → 𝟚 → 𝟚
false ⊃ y = true
true ⊃ y = y

{-
T : 𝟚 → Set
T true  = ⊤
T false = ⊥
-}
infix 0 dep-if_then_else_

dep-if_then_else_ : ∀{i}{A : 𝟚 → Set i}(b : 𝟚)(x : A true)(y : A false) → A b
dep-if true then x else y = x
dep-if false then x else y = y

infix 0 if_then_else_

if_then_else_ : ∀{i}{A : Set i} → 𝟚 → A → A → A
if b then t else f = dep-if b then t else f

ind𝟚 : ∀{i}(P : 𝟚 → Set i) → P true → P false → (t : 𝟚) → P t
ind𝟚 P x y true = x
ind𝟚 P x y false = y

infixr 6 default⇒_
infixr 5 case_⇒_break_
infixr 4.1 switch_cases_

switch_cases_ : ∀{i j} {A : Set i} {B : Set j} → (A → 𝟚) → ((A → 𝟚) → B) → B
switch caseIndicator cases caseData = caseData caseIndicator

case_⇒_break_ : ∀{i j} {A : Set i} {B : Set j} → A → B → (otherCases : (A → 𝟚) → B) → (A → 𝟚) → B
case forValue ⇒ result break otherCases = λ caseIndicator → if (caseIndicator forValue) then result else (otherCases caseIndicator)

default⇒_ : ∀{i j} {A : Set i} {B : Set j} → B → (A → 𝟚) → B
default⇒_ value caseIndicator = value