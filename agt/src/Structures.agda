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

  private
    +-cancelˡ-≤-pos-step : ∀ a b → + 1 + a ≤ + 1 + b → a ≤ b
    +-cancelˡ-≤-pos-step (+ _) (+ _) (+≤+ (ℕ.s≤s m≤n)) = +≤+ m≤n
    +-cancelˡ-≤-pos-step (+ _) -[1+ 0 ] (+≤+ ())
    +-cancelˡ-≤-pos-step -[1+ _ ] (+ _) _ = -≤+
    +-cancelˡ-≤-pos-step -[1+ 0 ] -[1+ 0 ] _ = -≤- ℕ.z≤n
    +-cancelˡ-≤-pos-step -[1+ ℕ.suc _ ] -[1+ 0 ] _ = -≤- ℕ.z≤n
    +-cancelˡ-≤-pos-step -[1+ ℕ.suc _ ] -[1+ ℕ.suc _ ] (-≤- n≤m) = -≤- (ℕ.s≤s n≤m)

    +-cancelˡ-≤-neg-step : ∀ a b → -[1+ 0 ] + a ≤ -[1+ 0 ] + b → a ≤ b
    +-cancelˡ-≤-neg-step (+ 0) (+ _) _ = +≤+ ℕ.z≤n
    +-cancelˡ-≤-neg-step +[1+ _ ] +[1+ _ ] (+≤+ m≤n) = +≤+ (ℕ.s≤s m≤n)
    +-cancelˡ-≤-neg-step -[1+ _ ] (+ _) _ = -≤+
    +-cancelˡ-≤-neg-step -[1+ _ ] -[1+ _ ] (-≤- (ℕ.s≤s n≤m)) = -≤- n≤m
    +-cancelˡ-≤-neg-step (+ 0) -[1+ _ ] (-≤- ())

  +-cancelˡ-≤ : LeftCancellative _≤_ _+_
  +-cancelˡ-≤ (+ 0) {a} {b} P rewrite +-identityˡ a | +-identityˡ b = P
  +-cancelˡ-≤ +[1+ n ] {b} {c} P rewrite +-assoc (+ 1) (+ n) b | +-assoc (+ 1) (+ n) c = +-cancelˡ-≤ (+ n) (+-cancelˡ-≤-pos-step _ _ P)
  +-cancelˡ-≤ -[1+ 0 ] {b} {c} P = +-cancelˡ-≤-neg-step _ _ P
  +-cancelˡ-≤ -[1+ ℕ.suc n ] {b} {c} P rewrite +-assoc -[1+ 0 ] -[1+ n ] b | +-assoc -[1+ 0 ] -[1+ n ] c = +-cancelˡ-≤ -[1+ n ] (+-cancelˡ-≤-neg-step _ _ P)

  +-cancelʳ-≤ : RightCancellative _≤_ _+_
  +-cancelʳ-≤ {c} a b P rewrite +-comm a c | +-comm b c = +-cancelˡ-≤ c P

  +-cancel-≤ : Cancellative _≤_ _+_
  +-cancel-≤ = +-cancelˡ-≤ , +-cancelʳ-≤

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
