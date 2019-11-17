module Overture.Show where

open import Data.Fin as 𝔽 using (Fin)
open import Data.List using (List; _∷_; [])
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Show as ℕˢ
open import Data.String using (String)
open import Data.Vec using (Vec; _∷_; [])
open import Function using (_∘_)
open import Text.Printf using (printf)

showℕ = ℕˢ.show

show𝔽 : ∀ {n} → Fin n → String
show𝔽 = showℕ ∘ 𝔽.toℕ

show𝕍 : ∀ {ℓ} {n} {A : Set ℓ} → (A → String) → Vec A n → String
show𝕍 showA [] = printf "[]"
show𝕍 {_} {_} {A} showA as@(_ ∷ _) = go "[" as
  where go : ∀ {n} → String → Vec A (ℕ.suc n) → String
        go acc (a ∷ []) = printf "%s%s]" acc (showA a)
        go acc (a ∷ bs@(_ ∷ _)) = go (printf "%s%s, " acc (showA a)) bs

show𝕃 : ∀ {ℓ} {A : Set ℓ} → (A → String) → List A → String
show𝕃 {_} {A} showA = go "["
  where go : String → List A → String
        go acc [] = printf "%s]" acc
        go acc (a ∷ []) = printf "%s%s]" acc (showA a)
        go acc (a ∷ bs@(_ ∷ _)) = go (printf "%s%s, " acc (showA a)) bs
