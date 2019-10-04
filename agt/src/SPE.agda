open import AGT
open import Utils

open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡-refl)

open import Relation.Nullary
open import Data.Nat using (ℕ)
open import Data.Fin as F using (Fin; 0F)
open import Data.Vec as V using (Vec; _∷_)
open import Data.Vec.All as A using (All)
open import Data.Product
open import Function.Injection using (Injection; _↣_)
open import Level using (_⊔_; suc)
open import Function using (_|>_; _$_)
open import Relation.Unary
import Algebra.Morphism as M

module SPE (c : Currency ℓ ℓ₁ ℓ₂) (a : Allotment ℓ ℓ₁ ℓ₂) (n : ℕ)
           {h : _} (H : M.IsRingMorphism (Allotment.ring a) (Currency.ring c) h)
           {X : Set ℓ} (Feasible : X ↣ Vec (Allotment.A a) n)
           where

C = Currency.A c
A = Allotment.A a
Bid = Vec C n
Allocation = Vec A n
Payment = Vec C n
Utility = Vec C n

record Valuation : Set (ℓ ⊔ ℓ₂) where
  open Currency c
  field
    valuations : Vec C n
    valuationsAreNonNegtive : {i : Fin n} → 0# ≤ V.lookup valuations i

record DirectRelevation : Set (suc (ℓ ⊔ ℓ₂)) where
  field
    valuation : Valuation
    allocation : Bid → X
    payment : Bid → Payment

  open Valuation valuation
  open Currency c

  module _ (b : Bid) where
    as = let open Injection in V.map h $ Feasible ⟨$⟩ allocation b
    vbap = V.zip valuations $ V.zip b $ V.zip as $ payment b

    truthful : Pred (Fin n) ℓ₁
    truthful i with V.lookup vbap i
    ... | (vᵢ , bᵢ , _ ) = vᵢ ≈ bᵢ

    quasiLinear : Pred Utility (ℓ ⊔ ℓ₁)
    quasiLinear us = All (λ { (uᵢ , vᵢ , _ , aᵢ , pᵢ) → uᵢ ≈ vᵢ * aᵢ - pᵢ }) (V.zip us vbap)

    nonNegativeUtility : {i : Fin n} {u : Utility}
                       → truthful i -> quasiLinear u
                       → All (λ { (_ , bᵢ , aᵢ , pᵢ) → (0# ≤ pᵢ) × (pᵢ ≤ (bᵢ * aᵢ)) }) vbap
                       → 0# ≤ V.lookup u i
    nonNegativeUtility {i} {u} t ql p with A.lookup i ql | A.lookup i p
    ... | Q | (Pzn , P) with V.lookup vbap i | proj₂ (V.lookup (V.zip u vbap) i) | proj₂-zip-lookup u vbap i
    ... | _ | (vᵢ , bᵢ , aᵢ , pᵢ) | ≡-refl with proj₁ (V.lookup (V.zip u vbap) i) | proj₁-zip-lookup u vbap i
    ... | _ | ≡-refl with V.lookup u i
    ... | uᵢ with trans (trans (+-cong Q refl) (trans (+-assoc _ _ _) (+-cong refl (-‿inverseˡ pᵢ)))) (+-identityʳ _)
    ... | I with ≤-respʳ-≈ (sym (trans I (*-congʳ t))) P
    ... | K = {!!}
