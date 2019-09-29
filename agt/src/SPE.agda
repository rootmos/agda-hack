open import AGT
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec as V using (Vec)
open import Function.Injection using (_↣_)
open import Level using (suc)

module SPE (c : Currency ℓ ℓ₁ ℓ₂) (a : Allotment ℓ) (n : ℕ) where

open Currency c renaming (A to C)
open Allotment a renaming (A to A)

record Valuation (V : Vec C n) : Set ℓ₂ where
  field
    valuationsAreNonNegtive : {i : Fin n} → 0# ≤ V.lookup V i

Bid = Vec C n
Allocation = Vec A n
Payment = Vec C n

record Feasible : Set (suc ℓ) where
  field
    X : Set ℓ
    feasibleInj : X ↣ Allocation

AllocationRule = Bid → Feasible
PaymentRule = Bid → Payment
