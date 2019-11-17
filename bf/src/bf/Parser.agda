module bf.Parser where

import Util as 𝕌
open import bf.Lexer

open import Data.Fin as 𝔽 using (Fin)
open import Data.Maybe as 𝕄 using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ) renaming (_≟_ to _≟ℕ_)
import Data.Nat.Properties as ℕᵖ
open import Data.List using (List; _∷_; [])
open import Data.Product as ℙ using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec as 𝕍 using (Vec; _∷_; [])
import Data.Vec.Categorical as 𝕍ᶜ
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
import Data.Sum.Categorical.Left as ⊎
open import Data.String using (String)
open import Function using (_$_; _|>_; _∘_; id)
open import Relation.Nullary using (yes; no)
open import Text.Printf using (printf)

data Op : Set where
  inc : Op
  dec : Op

data PtrArith : Set where
  inc : PtrArith
  dec : PtrArith

data Cond : Set where
  z : Cond
  nz : Cond

data Effect : Set where
  noop : Effect
  input : Effect
  output : Effect
  op : Op → Effect
  pointer : PtrArith → Effect
  cond : Cond → Effect

showEffect : Effect → String
showEffect noop = "noop"
showEffect input = "input"
showEffect output = "output"
showEffect (op inc) = "op(inc)"
showEffect (op dec) = "op(dec)"
showEffect (pointer inc) = "pointer(inc)"
showEffect (pointer dec) = "pointer(dec)"
showEffect (cond z) = "cond(z)"
showEffect (cond nz) = "cond(nz)"

data Error : Set where
  unmatched : Token → Error
  unimplemented : Error

Label : ℕ → Set
Label n = ⊤ ⊎ Fin n

showLabel : ∀ {n} → Label n → String
showLabel (inj₁ tt) = "∙"
showLabel (inj₂ i) = 𝕌.show𝔽 i

record Edge n : Set where
  field
    base target : Label n
    effect : Effect
    source : Maybe Token

showEdge : ∀ {n} → Edge n → String
showEdge record { base = b ; target = t ; effect = e ; source = just k} =
  printf "%s→%s %s %s" (showLabel b) (showLabel t) (showEffect e) (showToken k)
showEdge record { base = b ; target = t ; effect = e ; source = nothing } =
  printf "%s→%s %s" (showLabel b) (showLabel t) (showEffect e)

record Graph : Set where
  field
    size : ℕ
    edges : Label size → List (Edge size)

module _ n where
  private
    L = Label n
    E = Edge n
    Raw = Vec Token n

  terminal : L
  terminal = inj₁ tt

  initial : L
  initial = inj₁ tt

  private
    mk : Token → Fin n → Effect → E
    mk t b e with n ≟ℕ ℕ.suc (𝔽.toℕ b)
    ... | yes _ = record { base = inj₂ b ; target = terminal ; effect = e; source = just t }
    ... | no P = record { base = inj₂ b ; target = inj₂ $ 𝔽.lower₁ (𝔽.suc b) P; effect = e; source = just t }

    brackets : Token → Maybe 𝕌.Bracket
    brackets (jz _) = just 𝕌.op
    brackets (jnz _) = just 𝕌.cl
    brackets _ = nothing

  interpretToken : Raw → Token → Fin n → Error ⊎ List E
  interpretToken _ t@(inc _) b = inj₂ $ mk t b (op inc) ∷ []
  interpretToken _ t@(dec _) b = inj₂ $ mk t b (op dec) ∷ []
  interpretToken _ t@(left _) b = inj₂ $ mk t b (pointer inc) ∷ []
  interpretToken _ t@(right _) b = inj₂ $ mk t b (pointer dec) ∷ []
  interpretToken _ t@(input _) b = inj₂ $ mk t b input ∷ []
  interpretToken _ t@(output _) b = inj₂ $ mk t b output ∷ []
  interpretToken _ t@(comment _ _) b = inj₂ $ mk t b noop ∷ []
  interpretToken raw t@(jz _) b with mk t b
  ... | mk′ rewrite proj₂ (𝕌.excSplitℕ b) =
    𝕌.match brackets (𝕍.drop (𝔽.toℕ b) raw) |> 𝕄.maybe′ f (inj₁ (unmatched t))
      where f = λ j → inj₂ $ record (mk′ $ cond z) { target = inj₂ (𝔽.raise _ j) } ∷ mk′ noop ∷ []
  interpretToken raw t@(jnz _) b with mk t b
  ... | mk′ rewrite proj₂ (𝕌.incSplitℕ b) =
    𝕌.match (𝕌.flip brackets) (𝕍.reverse $ 𝕍.take _ raw) |> 𝕄.maybe′ f (inj₁ $ unmatched t)
      where go : ∀ k → Fin (ℕ.suc (𝔽.toℕ b)) → Fin (ℕ.suc (𝔽.toℕ b ℕ.+ k))
            go k j with 𝔽.inject+ (𝔽.toℕ j) (𝔽.toℕ b 𝔽.ℕ- j)
            ... | l rewrite ℕᵖ.m∸n+n≡m (𝕌.toℕ-≤ j) = 𝔽.inject+ k l
            f = λ j → inj₂ $ record (mk′ $ cond nz) { target = inj₂ $ go _ j } ∷ mk′ noop ∷ []

graph : ∀ {n} → Vec Token n → Error ⊎ Graph
graph {0} ts = inj₂ $ record { size = 0 ; edges = λ _ → record { base = initial _ ; target = terminal _ ; effect = noop ; source = nothing } ∷ [] }
graph {n@(ℕ.suc _)} ts = map₂ (λ es → record { size = n ; edges = edges es }) $
  M.sequenceA $ 𝕍.zip ts (𝕍.tabulate id) |> 𝕍.map λ { (t , b) → interpretToken n ts t b }
    where module M {ℓ} = 𝕍ᶜ.TraversableA {ℓ} {n} (⊎.applicative Error ℓ)
          edges : Vec (List (Edge n)) n → Label n → List (Edge n)
          edges _ (inj₁ _) = record { base = initial _ ; target = inj₂ 𝔽.zero ; effect = noop ; source = nothing } ∷ []
          edges es (inj₂ i) = 𝕍.lookup es i

module _ (g : Graph) where
  private
    s = Graph.size g

  labels : Vec (Label s) (ℕ.suc s)
  labels = initial s ∷ 𝕍.tabulate inj₂

  showGraph : String
  showGraph = goG "{" $ labels
    where goL : Label s → String
          goL = 𝕌.show𝕃 showEdge ∘ Graph.edges g
          goG : ∀ {m} → String → Vec (Label s) m → String
          goG acc [] = printf "%s}" acc
          goG acc (l ∷ []) = printf "%s%s: %s}" acc (showLabel l) (goL l)
          goG acc (l ∷ ls@(_ ∷ _)) =
            goG (printf "%s%s: %s, " acc (showLabel l) (goL l)) ls
