open import AGT
open import Relation.Nullary
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec as V using (Vec)
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

    truthful : Pred (Fin n) ℓ₁
    truthful i = V.lookup valuations i ≈ V.lookup b i

    quasiLinear : Pred Utility (ℓ ⊔ ℓ₁)
    quasiLinear us = All (λ { (uᵢ , ((aᵢ , pᵢ) , vᵢ)) → uᵢ ≈ vᵢ * aᵢ - pᵢ }) xs
      where
        xs = V.zip us (V.zip (V.zip as (payment b)) valuations)

    nonNegativeUtility : {i : Fin n} {u : Utility}
                       → truthful i -> quasiLinear u
                       → All (λ { (pᵢ , (bᵢ , aᵢ)) → (0# ≤ pᵢ) × (pᵢ ≤ (bᵢ * aᵢ)) })
                             (V.zip (payment b) (V.zip b as))
                       → 0# ≤ V.lookup u i
    nonNegativeUtility {i} t ql p = let a = A.lookup i ql in {!!}
