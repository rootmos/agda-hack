module bf.Parser where

open import bf.Lexer

open import Overture.Show using (show𝔽; show𝕃)
import Overture.Match as Match
import Overture.Fin as 𝔽ᵒ

open import Data.Empty using (⊥-elim)
open import Data.Fin as 𝔽 using (Fin)
open import Data.Maybe as 𝕄 using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ) renaming (_≟_ to _≟ℕ_)
import Data.Nat.Properties as ℕᵖ
open import Data.List as 𝕃 using (List; _∷_; []; length)
open import Data.Product as ℙ using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec as 𝕍 using (Vec; _∷_; [])
import Data.Vec.Categorical as 𝕍ᶜ
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
import Data.Sum.Categorical.Left as ⊎
open import Data.String using (String)
open import Function using (_$_; _|>_; _∘_; id)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
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
showLabel (inj₂ i) = show𝔽 i

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

record EdgeLabel (g : Graph) : Set where
  constructor _,_
  field
    node : Label (Graph.size g)
    edge : Fin (length $ Graph.edges g node)

record Path (g : Graph) (l : ℕ) : Set where
  field
    edges : Vec (EdgeLabel g) l

  private
    [_] : Fin l → Edge (Graph.size g)
    [ i ] = let n , e = 𝕍.lookup edges i in 𝕃.lookup (Graph.edges g n) e

  field
    connected : {i : Fin l} → (P : l ≢ 𝔽.toℕ (𝔽.suc i))
              → Edge.target [ i ] ≡ Edge.base [ 𝔽.lower₁ _ P ]

base : ∀ {l} {g : Graph} → Path g (ℕ.suc l) → Label (Graph.size g)
base = {!!}

target : ∀ {l} {g : Graph} → Path g (ℕ.suc l) → Label (Graph.size g)
target = {!!}

emptyPath : (g : Graph) → Path g 0
emptyPath g = record { edges = [] ; connected = λ {i} → ⊥-elim $ lemma i }
  where lemma : ¬ Fin 0
        lemma ()

singletonPath : {g : Graph} → EdgeLabel g → Path g 1
singletonPath e = record { edges = e ∷ [] ; connected = λ {i} P → ⊥-elim $ P (lemma i) }
  where lemma : (i : Fin 1) → 1 ≡ ℕ.suc (𝔽.toℕ i)
        lemma 𝔽.zero = refl

join : ∀ {n} {m} {g : Graph} {p₀ : Path g (ℕ.suc n)} {p₁ : Path g (ℕ.suc m)}
     → target p₀ ≡ base p₁ → Path g (ℕ.suc n ℕ.+ ℕ.suc m)
join = {!!}

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

    brackets : Token → Maybe Match.Bracket
    brackets (jz _) = just Match.op
    brackets (jnz _) = just Match.cl
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
  ... | mk′ rewrite proj₂ (𝔽ᵒ.excSplitℕ b) =
    Match.match brackets (𝕍.drop (𝔽.toℕ b) raw) |> 𝕄.maybe′ f (inj₁ (unmatched t))
      where f = λ j → inj₂ $ record (mk′ $ cond z) { target = inj₂ (𝔽.raise _ j) } ∷ mk′ noop ∷ []
  interpretToken raw t@(jnz _) b with mk t b
  ... | mk′ rewrite proj₂ (𝔽ᵒ.incSplitℕ b) =
    Match.match (Match.flip brackets) (𝕍.reverse $ 𝕍.take _ raw) |> 𝕄.maybe′ f (inj₁ $ unmatched t)
      where go : ∀ k → Fin (ℕ.suc (𝔽.toℕ b)) → Fin (ℕ.suc (𝔽.toℕ b ℕ.+ k))
            go k j with 𝔽.inject+ (𝔽.toℕ j) (𝔽.toℕ b 𝔽.ℕ- j)
            ... | l rewrite ℕᵖ.m∸n+n≡m (𝔽ᵒ.toℕ-≤ j) = 𝔽.inject+ k l
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
          goL = show𝕃 showEdge ∘ Graph.edges g
          goG : ∀ {m} → String → Vec (Label s) m → String
          goG acc [] = printf "%s}" acc
          goG acc (l ∷ []) = printf "%s%s: %s}" acc (showLabel l) (goL l)
          goG acc (l ∷ ls@(_ ∷ _)) =
            goG (printf "%s%s: %s, " acc (showLabel l) (goL l)) ls
