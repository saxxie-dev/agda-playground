module Straw2 where
open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Univalence public
open import Agda.Builtin.Cubical.Glue using (_≃_)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism

-- We want to show that Straw ≡ Loop 

data Loop : Type where 
  p : Loop 
  loop : p ≡ p 

data Straw : Type where 
  a : Straw 
  b : Straw
  seam : a ≡ b 
  edge : a ≡ a 

Straw→Loop : Straw →  Loop 
Straw→Loop a = p
Straw→Loop b = p
Straw→Loop (seam i) = p
Straw→Loop (edge i) = loop i

Loop→Straw : Loop → Straw
Loop→Straw p = a
Loop→Straw (loop i) = edge i 

Straw≡Loop : Straw ≡ Loop 
Straw≡Loop = ua (isoToEquiv  
  (iso Straw→Loop Loop→Straw sect ret)) where 
    sect : section Straw→Loop Loop→Straw
    sect p = refl 
    sect (loop i) = refl
    ret : retract Straw→Loop Loop→Straw
    ret a = refl 
    ret b = seam
    ret (seam i) = λ j → seam (i ∧ j)
    ret (edge i) = refl

-- THAT WAS EASY!