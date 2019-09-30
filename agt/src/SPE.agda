open import AGT
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec as V using (Vec)
open import Data.Product using (_,_)
open import Function.Injection using (Injection; _↣_)
open import Level using (_⊔_; suc)
open import Function using (_|>_)

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

  quasiLinearUtility : Bid → Utility
  quasiLinearUtility b = V.map q (V.zip (V.zip as (payment b)) valuations)
    where
      open Injection
      as = Feasible ⟨$⟩ allocation b |> V.map h
      open Currency c
      q = λ { ((aᵢ , pᵢ) , vᵢ) → vᵢ * aᵢ - pᵢ }
