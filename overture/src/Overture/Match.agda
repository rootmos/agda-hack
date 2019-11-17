module Overture.Match where

open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Vec as 𝕍 using (Vec; _∷_; [])
open import Function using (id)

data Bracket : Set where
  op : Bracket
  cl : Bracket

module _ where
  open import Data.Char using (Char)

  square : Char → Maybe Bracket
  square '[' = just op
  square ']' = just cl
  square _ = nothing

flip : ∀ {ℓ} {a : Set ℓ} → (a → Maybe Bracket) → (a → Maybe Bracket)
flip f a with f a
flip f a | just op = just cl
flip f a | just cl = just op
flip f a | nothing = nothing

match : ∀ {ℓ} {a : Set ℓ} {n} → (a → Maybe Bracket) → Vec a n → Maybe (Fin n)
match {_} {a} {0} p as = nothing
match {_} {a} {ℕ.suc n} p as = go 0 (𝕍.zip as (𝕍.tabulate id))
  where go : ∀ {m} → ℕ → Vec (a × Fin (ℕ.suc n)) m → Maybe (Fin (ℕ.suc n))
        go l [] = nothing
        go l ((x , _) ∷ xs) with p x
        go l (_ ∷ xs) | just op = go (ℕ.suc l) xs
        go 0 (_ ∷ _) | just cl = nothing
        go 1 ((_ , i) ∷ xs) | just cl = just i
        go (ℕ.suc (ℕ.suc l)) (_ ∷ xs) | just cl = go (ℕ.suc l) xs
        go l (_ ∷ xs) | nothing = go l xs
