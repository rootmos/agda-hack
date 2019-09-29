module AGT where

open import Algebra using (Ring)
open import Algebra.Structures using (IsCommutativeRing)
open import Algebra.FunctionProperties using (Op₁; Op₂)

open import Relation.Binary using (Rel; IsPartialOrder)
open import Level using (Level; _⊔_; suc)

variable
  ℓ ℓ₁ ℓ₂ : Level

record Currency ℓ ℓ₁ ℓ₂ : Set (suc (ℓ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    A : Set ℓ
    _≈_ : Rel A ℓ₁
    _≤_ : Rel A ℓ₂
    + * : Op₂ A
    - : Op₁ A
    0# 1# : A
    isPartialOrder : IsPartialOrder _≈_ _≤_
    isCommutativeRing : IsCommutativeRing _≈_ + * - 0# 1#

record Allotment ℓ : Set (suc ℓ) where
  field 
    A : Set ℓ
