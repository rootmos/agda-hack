module AGT where

open import Algebra using (Ring)
open import Algebra.Structures using (IsCommutativeRing)
open import Algebra.FunctionProperties using (Op₁; Op₂)
open import Relation.Binary using (Rel; IsPartialOrder)
open import Level using (Level; _⊔_; suc)

private
  variable
    ℓ ℓ₁ ℓ₂ : Level

record Currency ℓ ℓ₁ ℓ₂ : Set (suc (ℓ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Unit : Set ℓ
    _≈_ : Rel Unit ℓ₁
    _≤_ : Rel Unit ℓ₂
    + * : Op₂ Unit
    - : Op₁ Unit
    0# 1# : Unit
    isPartialOrder : IsPartialOrder _≈_ _≤_
    isCommutativeRing : IsCommutativeRing _≈_ + * - 0# 1#

module Mk (C : Currency ℓ ℓ₁ ℓ₂) where
