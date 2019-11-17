module Overture.Fin where

open import Data.Fin as 𝔽 using (Fin)
open import Data.Nat as ℕ using (ℕ; _+_; _≤_)
open import Data.Product as ℙ using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

excSplitℕ : ∀ {n} → (i : Fin n) → Σ[ j ∈ ℕ ] n ≡ 𝔽.toℕ i + j
excSplitℕ {ℕ.suc n} 𝔽.zero = ℕ.suc n , refl
excSplitℕ {ℕ.suc n} (𝔽.suc i) = ℙ.map₂ (cong ℕ.suc) (excSplitℕ i)

incSplitℕ : ∀ {n} → (i : Fin n) → Σ[ j ∈ ℕ ] n ≡ (ℕ.suc (𝔽.toℕ i)) + j
incSplitℕ {ℕ.suc n} 𝔽.zero = n , refl
incSplitℕ {ℕ.suc n} (𝔽.suc i) = ℙ.map₂ (cong ℕ.suc) (incSplitℕ i)

toℕ-≤ : ∀ {n} → (i : Fin n) → 𝔽.toℕ i ≤ n
toℕ-≤ 𝔽.zero = ℕ.z≤n
toℕ-≤ (𝔽.suc i) = ℕ.s≤s (toℕ-≤ i)
