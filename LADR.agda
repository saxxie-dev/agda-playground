module LADR where 
open import Cubical.Foundations.Prelude

record Field  : Type₁ where 
  infixl 5 _∔_
  infixl 6 _×_
  field
    F : Type
    _∔_ : F → F → F 
    ∔-commute : ∀ (x y : F) → x ∔ y ≡ y ∔ x
    ∔-associate : ∀ (w x y : F) → (x ∔ y) ∔ w ≡ x ∔ (y ∔ w)
    z : F 
    ∔-l-id : ∀ (x : F) → z ∔ x ≡ x
    ∔-r-id : ∀ (x : F) → x ∔ z ≡ x
    -_ : F → F 
    -inverse : ∀ (x : F) → (x ∔ - x) ≡ z
    _×_ : F → F → F 
    _⁻¹ : F → F 
    ⁻¹-involution : ∀ (x : F) → (x ⁻¹) ⁻¹ ≡ x
    
record VectorSpace (Fld : Field) : Type₁ where 
  open Field Fld
  field 
    V : Type 
    e : V
    _·_ : F → V → V 

record VectorMorphism {F : Field} (V : VectorSpace F) (W : VectorSpace F) : Type₁ where 
  field 
    fn : VectorSpace.V V → VectorSpace.V W 
    ·-homo : ∀ (v : VectorSpace.V V) → (k : Field.F F) → fn (VectorSpace._·_ V k v) ≡ VectorSpace._·_ W k (fn v)
    +-homo : ∀ (v : VectorSpace.V V) → VectorSpace.V V -- h

