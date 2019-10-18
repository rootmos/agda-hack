{-# OPTIONS --allow-unsolved-metas #-}
open import Structures
import Utils as U

open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Nullary
open import Data.Nat using (ℕ)
open import Data.Fin as F using (Fin; 0F)
open import Data.Vec as V using (Vec; _∷_)
open import Data.Vec.All as A using (All)
open import Data.Product
open import Function.Equivalence using (_⇔_; equivalence)
open import Level using (_⊔_; suc)
open import Function using (_|>_; _$_)
open import Relation.Unary
import Algebra.Morphism as M

module SPE (ℂ : Currency ℓ ℓ₁ ℓ₂) (𝔸 : Allotment ℓ ℓ₁ ℓ₂) (n : ℕ)
           {h : _} (H : M.IsRingMorphism (Allotment.ring 𝔸) (Currency.ring ℂ) h)
           (Feasible : Pred (Allotment.A 𝔸) ℓ)
           where
open Currency ℂ renaming (A to C)
open Allotment 𝔸 using () renaming (A to A; _≤_ to _≤ᵃ_)

Allocation = Fin n → Σ[ x ∈ A ] Feasible x
Bid = Fin n → C
Payment = Fin n → C
Utility = Fin n → C
Valuation = Fin n → C -- TODO: is it possible to keep the non-negativity requirement? Σ (Fin n → C) (λ v → ∀ {i} → 0# ≤ v i)

UtilityModel = Valuation → Bid → Utility

DominantStrategy : (Bid → Utility) → Fin n → Pred C (ℓ ⊔ ℓ₂)
DominantStrategy um i bᵢ = ∀ (b₌ : Σ[ b ∈ Bid ] b i ≡ bᵢ) b → um b i ≤ um (proj₁ b₌) i

DSIC : Pred (Valuation → Bid → Utility) _
DSIC um = ∀ v i → DominantStrategy (um v) i (v i)

Monotone : Pred (Bid → Allocation) (ℓ ⊔ ℓ₂)
Monotone a = ∀ {i b₀ b₁} → b₀ i ≤ b₁ i
           → (proj₁ $ a b₀ i) ≤ᵃ (proj₁ $ a b₁ i)

record DirectRelevation : Set (suc (ℓ ⊔ ℓ₂)) where
  constructor DR
  field
    allocation : Bid → Allocation
    payment : Bid → Payment

  private
    aᶜ : Bid → Fin n → C
    aᶜ b i = h $ proj₁ $ allocation b i

  quasiLinear : Σ[ u ∈ (Valuation → Bid → Utility) ] ∀ v b i → u v b i ≡ v i * aᶜ b i - payment b i
  quasiLinear = (λ v b i → v i * aᶜ b i - payment b i) , λ _ _ _ → ≡-refl

  module _ (v : Valuation) (b : Bid) where
    private
      p = payment b
      a = aᶜ b

    truthful : Pred (Fin n) ℓ₁
    truthful i = v i ≈ b i

    nonNegativeUtility : (∀ i → p i ≤ (b i * a i))
                       → ∀ {i} → truthful i → 0# ≤ proj₁ quasiLinear v b i
    nonNegativeUtility P {i} t rewrite proj₂ quasiLinear v b i =
      let Q₀ = trans (+-identityʳ _) (*-congʳ t) in
      let Q₁ = trans (+-cong refl (-‿inverseˡ _)) Q₀ in
      let Q₂ = trans (+-assoc _ _ _) Q₁ in
      ≤-respʳ-≈ (sym Q₂) (P i)
        |> ≤-respˡ-≈ (sym $ +-identityˡ _)
        |> proj₂ +-cancel-≤ _ _

  Implementable : Set (ℓ ⊔ ℓ₂)
  Implementable = DSIC (proj₁ quasiLinear)

module Myerson where

  module _ {a} (M : Monotone a) where
    formula : Σ[ p ∈ (Bid → Payment) ] ∀ {i b} → b i ≈ 0# → p b i ≈ 0#
    formula = {!!}

    dr : DirectRelevation
    dr = DR a (proj₁ formula)

    isDSIC : DSIC (proj₁ $ DirectRelevation.quasiLinear dr)
    isDSIC v i (b₌ , pb₌) b with DirectRelevation.quasiLinear dr
    ... | (ql , Q) with Q b v i | proj₁ formula
    ... | Qb | F =
      let x = λ b → proj₁ $ DirectRelevation.allocation dr b i in
      let p = λ b → DirectRelevation.payment dr b i in
      {!!}

module _ {dr : DirectRelevation} (T : ∀ {x y} → h x ≤ h y → x ≤ᵃ y) where
  open DirectRelevation dr

  moveʳ : {a b c : C} → (a + b) ≤ c → a ≤ (c + - b)
  moveʳ P = proj₂ +-cancel-≤ _ _ $ ≤-respʳ-≈ (sym $ trans (+-assoc _ _ _) $ trans (+-congˡ $ -‿inverseˡ _) $ +-identityʳ _) P

  moveˡ : {a b c : C} → a ≤ (b + c) → (a + - b) ≤ c
  moveˡ P = {!!}

  implementable : Implementable ⇔ Monotone allocation
  implementable = equivalence to {!!}
    where
      to : Implementable → Monotone allocation
      to I {i} {y} {z} B with I y i (y , ≡-refl) z | I z i (z , ≡-refl) y
      ... | P₀ | Q₀ with payment y i | payment z i | z i | y i | h (proj₁ (allocation y i)) | h (proj₁ (allocation z i))
      ... | py | pz | zi | yi | ay | az =
        let P = moveˡ $ ≤-respʳ-≈ (+-assoc _ _ _) $ moveʳ P₀ in
        let Q = moveˡ $ ≤-respʳ-≈ (trans (sym $ +-congʳ $ +-comm _ _) (+-assoc _ _ _)) $ moveʳ $ ≤-respˡ-≈ (+-comm _ _) $ Q₀ in
        let R = ≤-trans P Q in
        T {!!}


