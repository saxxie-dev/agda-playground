module Straw where
open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Univalence public
open import Agda.Builtin.Cubical.Glue using (_≃_)
open import Cubical.Foundations.Path

import Agda.Builtin.Cubical.HCompU as HCompU
module Helpers = HCompU.Helpers
open import Cubical.Foundations.Isomorphism
open Helpers using (fiber)

-- data Loop : Type where 
--   p : Loop 
--   loop : p ≡ p 

-- data Straw : Type where 
--   a : Straw
--   b : Straw 
--   seam : a ≡ b 
--   edge : a ≡ a

-- data Straw' : Type where 
--   a' : Straw'
--   b' : Straw'
--   seam' : a' ≡ b' 
--   edge' : seam' ≡ seam'
  

-- horizontalCrossSection : ∀ i → seam i ≡ seam i 
-- horizontalCrossSection i  = (sym a≡seam-i ) ∙ edge ∙ a≡seam-i where 
--   a≡seam-i = (λ j → seam (i ∧ j))

-- bottomEdge : b ≡ b 
-- bottomEdge i = hcomp (λ j → λ {
--   (i = i0) → seam j ;
--   (i = i1 ) → seam j }) (edge i)

-- wall : Square seam seam edge bottomEdge 
-- wall i j = hfill (λ k → λ { 
--     (i = i0) → seam k ;
--     (i = i1 ) → seam k
--   }) (inS (edge i)) j

-- straw→loop : Straw → Loop
-- straw→loop a = p
-- straw→loop b = p
-- straw→loop (seam i) = p
-- straw→loop (edge i) = loop i

-- loop→straw : Loop → Straw 
-- loop→straw p = a
-- loop→straw (loop i) = edge i 

-- Straw≃Loop : Straw ≃ Loop
-- Straw≃Loop = isoToEquiv (iso straw→loop loop→straw sect ret) where 
--   sect : ∀ z → straw→loop (loop→straw z) ≡ z
--   sect p = refl
--   sect (loop i) = refl
--   ret : ∀ z → loop→straw (straw→loop z) ≡ z
--   ret a = refl
--   ret b = seam
--   ret (seam i) = λ j → seam (i ∧ j)
--   ret (edge i) = refl
  
-- Straw≡Loop : Straw ≡ Loop 
-- Straw≡Loop = ua Straw≃Loop

is-contractible : Type → Type 
is-contractible T = Σ T (λ x → ∀ (y : T) → x ≡ y)


open import Cubical.Data.Bool
Σ-evil : Type₁
Σ-evil = Σ Type (λ A → A) 

Σ-evil-1 : Σ-evil
Σ-evil-1 = Bool , true

Σ-evil-2 : Σ-evil
Σ-evil-2 = Bool , false




helper2 : ∀ {A : Type} {B : A → Type} {a a' : A} {b : B a} {b' : B a'} → (p : a ≡ a') → (transport (cong B p) b ≡ b') → ((a , b) ≡ (a' , b'))
helper2 {B = B} {a = a} {b = b} {b' = b'} = λ p → ((J (λ a'' p' → (b'' : B a'') → (transport (cong B p') b ≡ b'') → ((a , b) ≡ (a'' , b''))) helper3) p) b' where 
  helper3 : (b'' : B a) → transport (λ i → B (refl i)) b ≡ b'' → (a , b) ≡ (a , b'')
  helper3 b'' q = J (λ b''' x → (a , b) ≡ (a , b''')) {! transp (λ i → B a) i0 b !} q

Σ-pathp
  : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : ∀ i → A i → Type ℓ'}
  → {x : Σ _ (B i0)} {y : Σ _ (B i1)}
  → (p : PathP A (fst x) (fst y))
  → PathP (λ i → B i (p i)) (x .snd) (y .snd)
  → PathP (λ i → Σ (A i) (B i)) x y
Σ-pathp p q i = p i , q i



path→ua-pathp : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) {x : A} {y : B}
              → e .fst x ≡ y
              → PathP (λ i → ua e i) x y
path→ua-pathp = {!   !} 

not-inv : ∀ (y : Bool) → not (not y) ≡ y 
not-inv false = refl
not-inv true = refl

Sigma : (A : Type) (B : A → Type) → Type
Sigma A B = Σ A B
syntax Sigma A (λ x → b) = Σ x ꞉ A , b

_==_ : Σ-evil → Σ-evil → Type₁
x == y = PathP (λ _ →  Σ-evil) x y

annotated : ∀ {ℓ} (T : Type ℓ) → (x y : T) → Type ℓ
annotated T x y = PathP  _ → T x y 

syntax annotated T x y = x ≡ y [ T ] 

Bool-flip : Bool ≡ Bool 
Bool-flip = ua (isoToEquiv (iso not not not-inv not-inv))

WTΣ : (Bool , true) ≡ (Bool , false) [ Σ T ꞉ Type , T ]
WTΣ = Σ-pathp Bool-flip (path→ua-pathp refl)


