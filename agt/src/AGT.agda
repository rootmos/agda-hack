module AGT where

open import Algebra using (Ring; CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Algebra.FunctionProperties using (Op₁; Op₂)

open import Relation.Binary using (Rel; IsPartialOrder)
open import Level using (Level; _⊔_; suc)

variable
  ℓ ℓ₁ ℓ₂ : Level

record Currency ℓ ℓ₁ ℓ₂ : Set (suc (ℓ ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    A : Set ℓ
    _≈_ : Rel A ℓ₁
    _≤_ : Rel A ℓ₂
    _+_ _*_ : Op₂ A
    -_ : Op₁ A
    0# 1# : A
    isPartialOrder : IsPartialOrder _≈_ _≤_
    isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#

  open IsCommutativeRing isCommutativeRing public

  commutativeRing : CommutativeRing _ _
  commutativeRing = record { isCommutativeRing = isCommutativeRing }

  ring : Ring _ _
  ring = record { isRing = isRing }

record Allotment ℓ ℓ₁ ℓ₂ : Set (suc (ℓ ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field 
    A : Set ℓ
    _≈_ : Rel A ℓ₁
    _≤_ : Rel A ℓ₂
    _+_ _*_ : Op₂ A
    -_ : Op₁ A
    0# 1# : A
    isPartialOrder : IsPartialOrder _≈_ _≤_
    isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#

  open IsCommutativeRing isCommutativeRing public

  commutativeRing : CommutativeRing _ _
  commutativeRing = record { isCommutativeRing = isCommutativeRing }

  ring : Ring _ _
  ring = record { isRing = isRing }
