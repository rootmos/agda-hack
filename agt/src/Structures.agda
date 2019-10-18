module Structures where

open import Algebra using (Ring; CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Algebra.FunctionProperties using (Op₁; Op₂; Cancellative; LeftCancellative; RightCancellative)
open import Relation.Binary using (Rel; IsPartialOrder)
open import Level using (Level; _⊔_; suc)
open import Data.Product
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡-refl)

variable
  ℓ ℓ₁ ℓ₂ : Level

record Currency ℓ₁ ℓ₂ : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  infix  4 _≤_
  field
    A : Set
    _≈_ : Rel A ℓ₁
    _≤_ : Rel A ℓ₂
    _+_ _*_ : Op₂ A
    -_ : Op₁ A
    0# 1# : A
    isPartialOrder : IsPartialOrder _≈_ _≤_
    isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#
    +-cancel-≤ : Cancellative _≤_ _+_

  open IsCommutativeRing isCommutativeRing public
  open IsPartialOrder isPartialOrder public
    renaming (refl to ≤-refl; trans to ≤-trans) hiding (reflexive)

  commutativeRing : CommutativeRing _ _
  commutativeRing = record { isCommutativeRing = isCommutativeRing }

  ring : Ring _ _
  ring = record { isRing = isRing }

module Integer where
  open import Data.Integer
  open import Data.Integer.Properties
  open import Data.Nat as ℕ using (ℕ)

  +-cancelˡ-≤ : LeftCancellative _≤_ _+_
  +-cancelˡ-≤ (+ 0) {a} {b} P rewrite +-identityˡ a | +-identityˡ b = P
  +-cancelˡ-≤ (+ (ℕ.suc n)) {b} {c} P = +-cancelˡ-≤ (+ n) {!!}
  +-cancelˡ-≤ (-[1+_] n) P = {!!}

  +-cancel-≤ : Cancellative _≤_ _+_
  +-cancel-≤ = +-cancelˡ-≤ , {!!}

  isCurrency : Σ[ c ∈ Currency _ _ ] Currency.A c ≡ ℤ
  isCurrency = (C , ≡-refl)
    where C = record { isCommutativeRing = +-*-isCommutativeRing
                     ; isPartialOrder = ≤-isPartialOrder
                     ; +-cancel-≤ = +-cancel-≤
                     }

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
