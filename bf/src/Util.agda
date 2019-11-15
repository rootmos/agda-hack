module Util where

open import Data.Bool using (Bool; true; false)
open import Data.Fin as 𝔽 using (Fin; 0F)
open import Data.List as 𝕃 using (List; _∷_; [])
open import Data.Maybe as 𝕄 using (Maybe; nothing; just)
open import Data.Nat as ℕ using (ℕ; _+_; suc; _≤_)
open import Data.Nat.Show as ℕˢ
open import Data.Product as ℙ using (_×_; _,_; Σ-syntax)
open import Data.String as 𝕊 using (String)
open import Data.Vec as 𝕍 using (Vec; _∷_; [])
open import Function using (_$_; id; _∘_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Text.Printf using (printf)

private
  variable
    A : Set
    ℓ : Level

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

excSplitℕ : ∀ {n} → (i : Fin n) → Σ[ j ∈ ℕ ] n ≡ 𝔽.toℕ i + j
excSplitℕ {suc n} 0F = suc n , refl
excSplitℕ {suc n} (𝔽.suc i) = ℙ.map₂ (cong suc) (excSplitℕ i)

incSplitℕ : ∀ {n} → (i : Fin n) → Σ[ j ∈ ℕ ] n ≡ (suc (𝔽.toℕ i)) + j
incSplitℕ {suc n} 0F = n , refl
incSplitℕ {suc n} (𝔽.suc i) = ℙ.map₂ (cong suc) (incSplitℕ i)

module _ where
  open import Data.Nat
  toℕ-≤ : ∀ {n} → (i : Fin n) → 𝔽.toℕ i ≤ n
  toℕ-≤ 0F = z≤n
  toℕ-≤ (𝔽.suc i) = s≤s (toℕ-≤ i)

showℕ = ℕˢ.show

show𝔽 : ∀ {n} → Fin n → String
show𝔽 = showℕ ∘ 𝔽.toℕ

show𝕍 : ∀ {n} {A : Set ℓ} → (A → String) → Vec A n → String
show𝕍 showA [] = printf "[]"
show𝕍 {_} {_} {A} showA as@(_ ∷ _) = go "[" as
  where go : ∀ {n} → String → Vec A (ℕ.suc n) → String
        go acc (a ∷ []) = printf "%s%s]" acc (showA a)
        go acc (a ∷ bs@(_ ∷ _)) = go (printf "%s%s, " acc (showA a)) bs

show𝕃 : {A : Set ℓ} → (A → String) → List A → String
show𝕃 {_} {A} showA = go "["
  where go : String → List A → String
        go acc [] = printf "%s]" acc
        go acc (a ∷ []) = printf "%s%s]" acc (showA a)
        go acc (a ∷ bs@(_ ∷ _)) = go (printf "%s%s, " acc (showA a)) bs
