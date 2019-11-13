module bf where

open import Data.Bool using (Bool; not; true)
open import Data.Maybe as 𝕄 using (Maybe; nothing; just)
open import Data.List as 𝕃 using (List; []; _∷_)
open import Data.Char using (Char)
open import Data.Nat using (ℕ; _≟_) renaming (suc to nsuc)
open import Data.Vec as 𝕍 using (Vec)
open import Level using (Level; _⊔_; Lift) renaming (suc to lsuc)
open import Data.Integer as ℤ using (ℤ)
open import Data.Unit using (⊤; tt)
open import Function using (_|>_; _$_; flip; id)
open import Algebra using (Ring)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Fin as 𝔽 using (Fin; 0F)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

private
  variable
    n m : ℕ
    i j k l : ℤ
    ℓ ℓ₀ ℓ₁ : Level

data Token n : Set where
  inc : Token n
  dec : Token n
  left : Token n
  right : Token n
  input : Token n
  output : Token n
  jz : Fin n → Token n
  jnz : Fin n → Token n
  comment : Char -> Token n

token : Char -> Token n
token '+' = inc
token '-' = dec
token '<' = left
token '>' = right
token ',' = input
token '.' = output
token '[' = jz {!!}
token ']' = jnz {!!}
token c = comment c

tokenize : List Char -> List (Token n)
tokenize cs = 𝕃.map token cs

record Tape ℓ (V : Set ℓ₀) (F : ∀ {ℓ} → Set ℓ → Set ℓ) : Set (ℓ₀ ⊔ lsuc ℓ) where
  field
    Carrier : Set ℓ
    get : Carrier → ℤ → F (Maybe V)
    set : Carrier → ℤ → V → F (Lift ℓ₀ ⊤)

record Value ℓ c : Set (lsuc (c ⊔ ℓ)) where
  field
    Carrier : Set ℓ
    _≈_ : Rel Carrier c
    0# : Carrier
    _≈?0 : ∀ v → Dec (v ≈ 0#)
    suc : Carrier → Carrier
    pred : Carrier → Carrier

  default : Maybe Carrier → Carrier
  default c = 𝕄.fromMaybe 0# c

module Parser (value : Value ℓ₀ ℓ₁) where
  open Value value renaming (Carrier to V)

  data Effect : Set ℓ₀ where
    noop : Effect
    input : Effect
    output : Effect
    op : (V → V) → Effect
    pointer : (ℤ → ℤ) → Effect
    cond : (V → Bool) → Effect

  module _ n where
    L = ⊤ ⊎ Fin n
    terminal : L
    terminal = inj₁ tt

    initial : L
    initial = inj₁ tt

    record Edge : Set ℓ₀ where
      field
        base target : L
        effect : Effect
        source : Maybe (Fin n × Token n)

    private
      mk : Token n → Fin n → Effect → Edge
      mk t b e with n ≟ nsuc (𝔽.toℕ b)
      ... | yes _ = record { base = inj₂ b ; target = terminal ; effect = e; source = just (b , t) }
      ... | no P = record { base = inj₂ b ; target = inj₂ $ 𝔽.lower₁ (𝔽.suc b) P; effect = e; source = just (b , t) }

    go : Token n → Fin n → List Edge
    go t@inc b = mk t b (op suc) ∷ []
    go t@dec b = mk t b (op pred) ∷ []
    go t@left b = mk t b (pointer ℤ.pred) ∷ []
    go t@right b = mk t b (pointer ℤ.suc) ∷ []
    go t@input b = mk t b input ∷ []
    go t@output b = mk t b output ∷ []
    go t@(comment x) b = mk t b noop ∷ []
    go t@(jz T) b = record (mk t b $ cond $ λ v → ⌊ v ≈?0 ⌋) { target = inj₂ T } ∷ mk t b noop ∷ []
    go t@(jnz T) b = record (mk t b $ cond $ λ v → not ⌊ v ≈?0 ⌋) { target = inj₂ T } ∷ mk t b noop ∷ []

    record Graph : Set ℓ₀ where
      field
        edges : L → List Edge

  graph : Vec (Token n) n → Graph n
  graph {𝔽.0F} ts = record { edges = λ _ → record { base = initial _ ; target = terminal _ ; effect = noop ; source = nothing } ∷ [] }
  graph {nsuc n} ts = record { edges = edges }
    where es = 𝕍.zip ts (𝕍.tabulate id) |> 𝕍.map λ { (t , b) → go _ t b }
          edges : L (nsuc n) → List (Edge (nsuc n))
          edges (inj₁ _) = record { base = initial _ ; target = inj₂ 0F ; effect = noop ; source = nothing } ∷ []
          edges (inj₂ i) = 𝕍.lookup es i

module Interpreter (value : Value ℓ₀ ℓ₁) (F : ∀ {ℓ} → Set ℓ → Set ℓ) where
  open Value value renaming (Carrier to V)
  open Parser value using (Graph; L)

  record State ℓ : Set (lsuc (ℓ ⊔ ℓ₀)) where
    field
      tape : Tape ℓ V F
      pointer : ℤ
      program : ∃[ n ] (L n × Graph n)

  step : State ℓ → F (State ℓ)
  step s = {!!}
