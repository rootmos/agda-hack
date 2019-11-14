module bf where

import util as 𝕌

open import Data.Bool using (Bool; not; true)
open import Data.Maybe as 𝕄 using (Maybe; nothing; just)
open import Data.List as 𝕃 using (List; []; _∷_)
open import Data.Char using (Char)
open import Data.Nat as ℕ using (ℕ) renaming (_≟_ to _≟ℕ_)
import Data.Nat.Properties as ℕᵖ
open import Data.Vec as 𝕍 using (Vec)
import Data.Vec.Categorical as 𝕍ᶜ
open import Level using (Level; _⊔_; Lift) renaming (suc to lsuc)
open import Data.Integer as ℤ using (ℤ; +_) renaming (_≟_ to _≟ℤ_)
open import Data.Unit using (⊤; tt)
open import Function using (_|>_; _$_; flip; id; _∘_)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum.Categorical.Left as ⊎
open import Data.Product as ℙ using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Fin as 𝔽 using (Fin; 0F)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.String as 𝕊 using (String)
open import Text.Printf using (printf)

private
  variable
    n m : ℕ
    ℓ ℓ₀ ℓ₁ : Level

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

integer : Value _ _
integer = record { Carrier = ℤ
                 ; _≈_ = _≡_
                 ; 0# = + 0
                 ; _≈?0 = λ v → v ≟ℤ + 0
                 ; suc = ℤ.suc
                 ; pred = ℤ.pred
                 }

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
    data Error : Set where
      unmatched : Char → Error
      unimplemented : Error

    data Token : Set ℓ₀ where
      inc : Token
      dec : Token
      left : Token
      right : Token
      input : Token
      output : Token
      jz : Fin n → Token
      jnz : Fin n → Token
      comment : Char → Token

    showToken : Token → String
    showToken inc = "inc"
    showToken dec = "dec"
    showToken left = "left"
    showToken right = "right"
    showToken input = "input"
    showToken output = "output"
    showToken (jz i) = printf "jz(%i)" (+ (𝔽.toℕ i))
    showToken (jnz i) = printf "jnz(%i)" (+ (𝔽.toℕ i))
    showToken (comment c) = printf "%c" c

    token : Vec Char n → (Char × Fin n) → Error ⊎ Token
    token cs ('+' , _) = inj₂ inc
    token cs ('-' , _) = inj₂ dec
    token cs ('<' , _) = inj₂ left
    token cs ('>' , _) = inj₂ right
    token cs (',' , _) = inj₂ input
    token cs ('.' , _) = inj₂ output
    token cs ('[' , i) with jz | unmatched '['
    ... | J | E rewrite proj₂ (𝕌.excSplitℕ i) =
      𝕌.match 𝕌.square (𝕍.drop (𝔽.toℕ i) cs) |>
        𝕄.maybe′ (λ j → inj₂ $ J (𝔽.raise _ j)) (inj₁ E)
    token cs (']' , i) with jnz | unmatched ']' | 𝕌.incSplitℕ i
    ... | J | E | (k , P) rewrite P =
      𝕌.match (𝕌.flip 𝕌.square) (𝕍.reverse $ 𝕍.take _ cs) |>
        𝕄.maybe′ (inj₂ ∘ J ∘ go) (inj₁ E)
        where go : Fin (ℕ.suc (𝔽.toℕ i)) → Fin (ℕ.suc (𝔽.toℕ i ℕ.+ k))
              go j with 𝔽.inject+ (𝔽.toℕ j) ((𝔽.toℕ i) 𝔽.ℕ- j)
              ... | l rewrite ℕᵖ.m∸n+n≡m (𝕌.toℕ-≤ j) = 𝔽.inject+ k l
    token cs (c , _) = inj₂ $ comment c

    tokenize : Vec Char n -> Error ⊎ Vec Token n
    tokenize cs = M.sequenceA $ 𝕍.map (token cs) (𝕍.zip cs $ 𝕍.tabulate id)
      where module M = 𝕍ᶜ.TraversableA {ℓ₀} {n} (⊎.applicative Error ℓ₀)

    L = ⊤ ⊎ Fin n
    terminal : L
    terminal = inj₁ tt

    initial : L
    initial = inj₁ tt

    record Edge : Set ℓ₀ where
      field
        base target : L
        effect : Effect
        source : Maybe (Fin n × Token)

    private
      mk : Token → Fin n → Effect → Edge
      mk t b e with n ≟ℕ ℕ.suc (𝔽.toℕ b)
      ... | yes _ = record { base = inj₂ b ; target = terminal ; effect = e; source = just (b , t) }
      ... | no P = record { base = inj₂ b ; target = inj₂ $ 𝔽.lower₁ (𝔽.suc b) P; effect = e; source = just (b , t) }

    interpretToken : Token → Fin n → List Edge
    interpretToken t@inc b = mk t b (op suc) ∷ []
    interpretToken t@dec b = mk t b (op pred) ∷ []
    interpretToken t@left b = mk t b (pointer ℤ.pred) ∷ []
    interpretToken t@right b = mk t b (pointer ℤ.suc) ∷ []
    interpretToken t@input b = mk t b input ∷ []
    interpretToken t@output b = mk t b output ∷ []
    interpretToken t@(comment x) b = mk t b noop ∷ []
    interpretToken t@(jz T) b = record (mk t b $ cond $ λ v → ⌊ v ≈?0 ⌋) { target = inj₂ T } ∷ mk t b noop ∷ []
    interpretToken t@(jnz T) b = record (mk t b $ cond $ λ v → not ⌊ v ≈?0 ⌋) { target = inj₂ T } ∷ mk t b noop ∷ []

    record Graph : Set ℓ₀ where
      field
        edges : L → List Edge

  graph : Vec (Token n) n → Graph n
  graph {𝔽.0F} ts = record { edges = λ _ → record { base = initial _ ; target = terminal _ ; effect = noop ; source = nothing } ∷ [] }
  graph {ℕ.suc n} ts = record { edges = edges }
    where es = 𝕍.zip ts (𝕍.tabulate id) |> 𝕍.map λ { (t , b) → interpretToken _ t b }
          edges : L (ℕ.suc n) → List (Edge (ℕ.suc n))
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

module main where
  open import IO using (lift; run; sequence′; putStrLn)
  open import IO.Primitive hiding (putStrLn)
  import Codata.Musical.Colist as 𝕃ᶜ

  import Unix

  data Action : Set where
    debugLexer : Action
    debugParser : Action
    usageAction : Action

  record Settings : Set where
    field
      action : Action
      programFilename : String

  usage : {a : Set} → Maybe String → IO a
  usage _ = Unix.exit (Unix.failure $ + 2)

  parseArgs : List String → IO Settings
  parseArgs cs = go cs usageAction nothing
    where go : List String → Action → Maybe String → IO Settings
          go [] a _ = usage nothing
          go (s ∷ cs) a _ with s 𝕊.≟ "--lexer"
          go (s ∷ cs) _ obf | yes _ = go cs debugLexer obf
          go (s ∷ cs) a _ | no _ with s 𝕊.≟ "--parser"
          go (s ∷ cs) a obf | no _ | yes _ = go cs debugParser obf
          go (s ∷ []) a _ | no _ | no _ = return (record { action = a ; programFilename = s })
          go (s ∷ x ∷ cs) a obf | no ¬p | no ¬p₁ = usage nothing

  handleParserError : {v : Value ℓ ℓ₀} {a : Set} → Parser.Error v n ⊎ a → IO a
  handleParserError (inj₁ (Parser.unmatched c)) = Unix.die (printf "unmatched %c" c)
  handleParserError (inj₁ Parser.unimplemented) = Unix.die (printf "unimplemented")
  handleParserError (inj₂ a) = return a

  runAction : Settings → String → IO _
  runAction s raw with Settings.action s
  runAction s raw | debugLexer = do
    ts ← handleParserError $ Parser.tokenize integer _ (𝕊.toVec raw)
    run ∘ sequence′ $ 𝕃ᶜ.map (putStrLn ∘ Parser.showToken _ _) (𝕃ᶜ.fromList $ 𝕍.toList ts)
  runAction s raw | debugParser = Unix.die "not implemented"
  runAction s raw | usageAction = usage nothing

  main = do
    s ← Unix.getArgs >>= parseArgs
    raw ← readFiniteFile (Settings.programFilename s)
    runAction s raw
