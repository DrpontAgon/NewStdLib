{-# OPTIONS --safe #-}

module Bool.Base.Functions where

open import Bool.Base.Type
open import Unit.Base.Type
open import Empty.Base.Type

infixr 6 _β§_
infixr 5 _β¨_ _xor_

not : π β π
not true  = false
not false = true

_β§_ : π β π β π
true  β§ b = b
false β§ b = false

_β¨_ : π β π β π
true  β¨ b = true
false β¨ b = b

_xor_ : π β π β π
true  xor b = not b
false xor b = b

infixr 4.9 _β_

_β_ : π β π β π
false β y = true
true β y = y

ToType : π β Set
ToType true  = β€
ToType false = β₯

infix 0 dep-if_then_else_

dep-if_then_else_ : β{i}{A : π β Set i}(b : π)(x : A true)(y : A false) β A b
dep-if true then x else y = x
dep-if false then x else y = y

infix 0 if_then_else_

if_then_else_ : β{i}{A : Set i} β π β A β A β A
if b then t else f = dep-if b then t else f

indπ : β{i}(P : π β Set i) β P true β P false β (t : π) β P t
indπ P x y true = x
indπ P x y false = y

infixr 6 defaultβ_
infixr 5 case_β_break_
infixr 4.1 switch_cases_

switch_cases_ : β{i j} {A : Set i} {B : Set j} β (A β π) β ((A β π) β B) β B
switch caseIndicator cases caseData = caseData caseIndicator

case_β_break_ : β{i j} {A : Set i} {B : Set j} β A β B β (otherCases : (A β π) β B) β (A β π) β B
case forValue β result break otherCases = Ξ» caseIndicator β if (caseIndicator forValue) then result else (otherCases caseIndicator)

defaultβ_ : β{i j} {A : Set i} {B : Set j} β B β (A β π) β B
defaultβ_ value caseIndicator = value