module AGT where

open import Algebra using (Ring)
open import Algebra.Structures using (IsCommutativeRing)
open import Algebra.FunctionProperties using (Op₁; Op₂)
open import Relation.Binary using (Rel; IsPartialOrder)
open import Level using (Level; _⊔_; suc)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

private
  variable
    ℓ ℓ₁ ℓ₂ : Level

record Currency ℓ ℓ₁ ℓ₂ : Set (suc (ℓ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    unit : Set ℓ
    _≈_ : Rel unit ℓ₁
    _≤_ : Rel unit ℓ₂
    + * : Op₂ unit
    - : Op₁ unit
    0# 1# : unit
    isPartialOrder : IsPartialOrder _≈_ _≤_
    isCommutativeRing : IsCommutativeRing _≈_ + * - 0# 1#

record SPE (C : Currency ℓ ℓ₁ ℓ₂) (n : ℕ): Set (suc (ℓ ⊔ ℓ₁ ⊔ ℓ₂)) where
  open Currency C public

  field
    valuations : Fin n → unit
    valuationsAreNonNegtive : (i : Fin n) → 0# ≤ valuations i
