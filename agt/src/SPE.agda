open import AGT
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec as V using (Vec)
open import Function.Injection using (_↣_)
open import Level using (_⊔_; suc)

module SPE (c : Currency ℓ ℓ₁ ℓ₂) (a : Allotment ℓ) (n : ℕ) where

open Currency c renaming (A to C)
open Allotment a renaming (A to A)

record Valuation : Set (ℓ ⊔ ℓ₂) where
  field
    valuations : Vec C n
    valuationsAreNonNegtive : {i : Fin n} → 0# ≤ V.lookup valuations i

Bid = Vec C n
Allocation = Vec A n
Payment = Vec C n
Utility = Vec C n

record Feasible : Set (suc ℓ) where
  field
    X : Set ℓ
    feasibleInj : X ↣ Allocation

record DirectRelevation : Set (suc (ℓ ⊔ ℓ₂)) where
  field
    valuation : Valuation
    allocation : Bid → Feasible
    payment : Bid → Payment

  open Valuation valuation

  quasiLinearUtility : Bid -> Utility
  quasiLinearUtility b = {!!}
