open import Algebra using (Ring; CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Algebra.FunctionProperties using (Op₁; Op₂; Cancellative; LeftCancellative; RightCancellative)
open import Relation.Binary
open import Level using (Level; _⊔_; suc)
open import Data.Product
open import Data.Sum
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡-refl)
open import Function using (_$_)

module Structures where

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
    +-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
    zeroProduct : ∀ {a b} → a * b ≈ 0# → a ≈ 0# ⊎ b ≈ 0#

  open IsCommutativeRing isCommutativeRing public
  open IsPartialOrder isPartialOrder public
    renaming (refl to ≤-refl; trans to ≤-trans) hiding (reflexive)

  commutativeRing : CommutativeRing _ _
  commutativeRing = record { isCommutativeRing = isCommutativeRing }

  ring : Ring _ _
  ring = record { isRing = isRing }

  poset : Poset _ _ _
  poset = record { isPartialOrder = isPartialOrder }

  module _ where
    open import Relation.Binary.Reasoning.PartialOrder poset

    +-cancelˡ-≤ : LeftCancellative _≤_ _+_
    +-cancelˡ-≤ x {y} {z} P = begin
      y ≈˘⟨ +-identityˡ _ ⟩
      0# + y ≈⟨ +-cong (sym $ -‿inverseˡ _) refl ⟩
      - x + x + y ≈⟨ +-assoc _ _ _ ⟩
      - x + (x + y) ≤⟨ +-mono-≤ ≤-refl P ⟩
      - x + (x + z) ≈˘⟨ +-assoc _ _ _ ⟩
      - x + x + z ≈⟨ +-cong (-‿inverseˡ _) refl ⟩
      0# + z ≈⟨ +-identityˡ _ ⟩
      z ∎

    +-cancelʳ-≤ : RightCancellative _≤_ _+_
    +-cancelʳ-≤ {z} x y P = +-cancelˡ-≤ z $ begin
       z + x ≈⟨ +-comm _ _ ⟩
       x + z ≤⟨ P ⟩
       y + z ≈⟨ +-comm _ _ ⟩
       z + y ∎

    +-cancel-≤ : Cancellative _≤_ _+_
    +-cancel-≤ = (+-cancelˡ-≤ , +-cancelʳ-≤)

module Integer where
  open import Data.Integer
  open import Data.Integer.Properties
  open import Data.Nat as ℕ using (ℕ)
  import Data.Nat.Properties as ℕₚ

  zeroProduct : ∀ {a b} → a * b ≡ +0 → a ≡ +0 ⊎ b ≡ +0
  zeroProduct {_} {b} _ with signAbs b
  zeroProduct {_} {.+0} _ | s ◂ 0 = inj₂ ≡-refl
  zeroProduct {a} {.(s ◃ ℕ.suc n)} P | s ◂ ℕ.suc n
    rewrite abs-◃ s (ℕ.suc n) with ℕₚ.m*n≡0⇒m≡0∨n≡0 ∣ a ∣ (abs-cong {s₂ = s} P)
  ... | inj₁ R = inj₁ (∣n∣≡0⇒n≡0 R)

  isCurrency : Σ[ c ∈ Currency _ _ ] Currency.A c ≡ ℤ
  isCurrency = (C , ≡-refl)
    where C = record { isCommutativeRing = +-*-isCommutativeRing
                     ; isPartialOrder = ≤-isPartialOrder
                     ; zeroProduct = zeroProduct
                     ; +-mono-≤ = +-mono-≤
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
