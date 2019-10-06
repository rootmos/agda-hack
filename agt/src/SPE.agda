open import AGT
import Utils as U

open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Nullary
open import Data.Nat using (ℕ)
open import Data.Fin as F using (Fin; 0F)
open import Data.Vec as V using (Vec; _∷_)
open import Data.Vec.All as A using (All)
open import Data.Product
open import Function.Equivalence using (_⇔_)
open import Function.Injection using (Injection; _↣_)
open Function.Injection.Injection
open import Level using (_⊔_; suc)
open import Function using (_|>_; _$_)
open import Relation.Unary
import Algebra.Morphism as M

module SPE (ℂ : Currency ℓ ℓ₁ ℓ₂) (𝔸 : Allotment ℓ ℓ₁ ℓ₂) (n : ℕ)
           {h : _} (H : M.IsRingMorphism (Allotment.ring 𝔸) (Currency.ring ℂ) h)
           {X : Set ℓ} (Feasible : X ↣ (Fin n → Allotment.A 𝔸))
           where
open Currency ℂ renaming (A to C)
open Allotment 𝔸 using () renaming (A to A; _≤_ to _≤ᵃ_)

Bid = Fin n → C
Payment = Fin n → C
Utility = Fin n → C
Valuation = Σ (Fin n → C) (λ v → ∀ {i} → 0# ≤ v i)

UtilityModel = Bid → Utility

DominantStrategy : UtilityModel → Fin n → Pred C (ℓ ⊔ ℓ₂)
DominantStrategy um i bᵢ = ∀ (b₌ : Σ[ b ∈ Bid ] b i ≡ bᵢ) b → um b i ≤ um (proj₁ b₌) i

DSIC : UtilityModel -> Valuation → _
DSIC um (v , _) = ∀ i → DominantStrategy um i (v i)

Monotone : Pred (Bid → X) (ℓ ⊔ ℓ₂)
Monotone a = ∀ {i b₀ b₁} → b₀ i ≤ b₁ i
           → (Feasible ⟨$⟩ a b₀ $ i) ≤ᵃ (Feasible ⟨$⟩ a b₁ $ i)

record DirectRelevation : Set (suc (ℓ ⊔ ℓ₂)) where
  constructor DR
  field
    valuation : Valuation
    allocation : Bid → X
    payment : Bid → Payment

  private
    v = proj₁ valuation
    aᶜ : Bid → Fin n → C
    aᶜ b i = h $ Feasible ⟨$⟩ allocation b $ i

  quasiLinear : Σ[ u ∈ UtilityModel ] ∀ b i → u b i ≡ v i * aᶜ b i - payment b i
  quasiLinear = (λ b i → v i * aᶜ b i - payment b i) , λ _ _ → ≡-refl

  module _ (b : Bid) where
    private
      p = payment b
      a = aᶜ b

    truthful : Pred (Fin n) ℓ₁
    truthful i = v i ≈ b i

    nonNegativeUtility : (∀ i → p i ≤ (b i * a i))
                       → ∀ {i} → truthful i → 0# ≤ proj₁ quasiLinear b i
    nonNegativeUtility P {i} t rewrite proj₂ quasiLinear b i =
      let Q₀ = trans (+-identityʳ _) (*-congʳ t) in
      let Q₁ = trans (+-cong refl (-‿inverseˡ _)) Q₀ in
      let Q₂ = trans (+-assoc _ _ _) Q₁ in
      ≤-respʳ-≈ (sym Q₂) (P i)
        |> ≤-respˡ-≈ (sym $ +-identityˡ _)
        |> proj₂ +-cancel-≤ _ _

Implementable : UtilityModel → Pred DirectRelevation (ℓ ⊔ ℓ₂)
Implementable um dr = DSIC um (DirectRelevation.valuation dr)

module Myerson (um : UtilityModel) (v : Valuation) where

  module _ {a} (M : Monotone a) where
    formula : Σ[ p ∈ (Bid → Payment) ] ∀ {i b} → b i ≈ 0# → p b i ≈ 0#
    formula = {!!}

    dr : DirectRelevation
    dr = DR v a (proj₁ formula)

    isDSIC : DSIC um v
    isDSIC = {!!}

  implementable : ∀ {dr a} → Implementable um dr ⇔ Monotone a
  implementable = {!!}
