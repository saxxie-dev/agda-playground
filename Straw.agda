module Straw where
open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Univalence public
open import Agda.Builtin.Cubical.Glue using (_≃_)
open import Cubical.Foundations.Path

import Agda.Builtin.Cubical.HCompU as HCompU
module Helpers = HCompU.Helpers
open import Cubical.Foundations.Isomorphism
open Helpers using (fiber)

data Loop : Type where 
  p : Loop 
  loop : p ≡ p 

data Straw : Type where 
  a : Straw
  b : Straw 
  seam : a ≡ b 
  edge : a ≡ a

data Straw' : Type where 
  a' : Straw'
  b' : Straw'
  seam' : a' ≡ b' 
  edge' : seam' ≡ seam'
  

horizontalCrossSection : ∀ i → seam i ≡ seam i 
horizontalCrossSection i  = (sym a≡seam-i ) ∙ edge ∙ a≡seam-i where 
  a≡seam-i = (λ j → seam (i ∧ j))

bottomEdge : b ≡ b 
bottomEdge i = hcomp (λ j → λ {
  (i = i0) → seam j ;
  (i = i1 ) → seam j }) (edge i)

wall : Square seam seam edge bottomEdge 
wall i j = hfill (λ k → λ { 
    (i = i0) → seam k ;
    (i = i1 ) → seam k
  }) (inS (edge i)) j

Straw≡Loop : Straw ≡ Loop 
Straw≡Loop = ua {!   !} 


straw→loop : Straw → Loop
straw→loop a = p
straw→loop b = p
straw→loop (seam i) = p
straw→loop (edge i) = loop i

loop→straw : Loop → Straw 
loop→straw p = a
loop→straw (loop i) = edge i 

straw≃loop : Straw ≃ Loop
straw≃loop = isoToEquiv (iso straw→loop loop→straw sect ret) where 
  sect : ∀ z → straw→loop (loop→straw z) ≡ z
  sect p = refl
  sect (loop i) = refl
  ret : ∀ z → loop→straw (straw→loop z) ≡ z
  ret a = refl
  ret b = seam
  ret (seam i) = λ j → seam (i ∧ j)
  ret (edge i) = refl
  
strawIsLoop : Straw ≡ Loop 
strawIsLoop = ua straw≃loop
  
  