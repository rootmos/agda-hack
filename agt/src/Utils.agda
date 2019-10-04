open import Relation.Binary.PropositionalEquality
open import Data.Vec as V using (Vec; _∷_)
open import Data.Product
open import Data.Fin as F using (0F)

-- These things are almost certainly proven elsewhere, but reimplemented as an exercise for the author
module Utils where

proj₁-zip-lookup : ∀ {n ℓ₀} {A B : Set ℓ₀} (a : Vec A n) (b : Vec B n)
                 → ∀ i → proj₁ (V.lookup (V.zip a b) i) ≡ V.lookup a i
proj₁-zip-lookup (a ∷ as) (b ∷ bs) 0F = refl
proj₁-zip-lookup (_ ∷ as) (_ ∷ bs) (F.suc i) = proj₁-zip-lookup as bs i

proj₂-zip-lookup : ∀ {n ℓ₀} {A B : Set ℓ₀} (a : Vec A n) (b : Vec B n)
                 → ∀ i → proj₂ (V.lookup (V.zip a b) i) ≡ V.lookup b i
proj₂-zip-lookup (a ∷ as) (b ∷ bs) 0F = refl
proj₂-zip-lookup (_ ∷ as) (_ ∷ bs) (F.suc i) = proj₂-zip-lookup as bs i
