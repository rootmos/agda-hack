module util where

open import Data.Bool using (Bool; true; false)
open import Data.Nat as ℕ using (ℕ; _+_; suc; _≤_)
open import Data.Vec as 𝕍 using (Vec; _∷_; [])
open import Data.Maybe as 𝕄 using (Maybe; nothing; just)
open import Data.Fin as 𝔽 using (Fin; 0F)
open import Data.Product as ℙ using (_×_; _,_; Σ-syntax)
open import Function using (_$_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

private
  variable
    A : Set

data Bracket : Set where
  op : Bracket
  cl : Bracket

module _ where
  open import Data.Char using (Char)

  square : Char → Maybe Bracket
  square '[' = just op
  square ']' = just cl
  square _ = nothing

flip : (A → Maybe Bracket) → (A → Maybe Bracket)
flip f a with f a
flip f a | just op = just cl
flip f a | just cl = just op
flip f a | nothing = nothing

match : ∀ {n} → (A → Maybe Bracket) → Vec A n → Maybe (Fin n)
match {A} {0F} p as = nothing
match {A} {suc n} p as = go 0 (𝕍.zip as (𝕍.tabulate id))
  where go : ∀ {m} → ℕ → Vec (A × Fin (suc n)) m → Maybe (Fin (suc n))
        go l [] = nothing
        go l ((x , _) ∷ xs) with p x
        go l (_ ∷ xs) | just op = go (suc l) xs
        go 0 (_ ∷ _) | just cl = nothing
        go 1 ((_ , i) ∷ xs) | just cl = just i
        go (suc (suc l)) (_ ∷ xs) | just cl = go (suc l) xs
        go l (_ ∷ xs) | nothing = go l xs

splitℕ : ∀ {n} → (i : Fin n) → Σ[ j ∈ ℕ ] n ≡ 𝔽.toℕ i + j
splitℕ {suc n} 0F = suc n , refl
splitℕ {suc n} (𝔽.suc i) = ℙ.map₂ (cong suc) (splitℕ i)
