module bf where

import util as 𝕌

open import Data.Bool using (Bool; not; true)
open import Data.Maybe as 𝕄 using (Maybe; nothing; just)
open import Data.List as 𝕃 using (List; []; _∷_)
open import Data.Char using (Char)
open import Data.Nat as ℕ using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Show renaming (show to showℕ)
import Data.Nat.Properties as ℕᵖ
open import Data.Vec as 𝕍 using (Vec)
import Data.Vec.Categorical as 𝕍ᶜ
open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
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

  show𝔽 : Fin n → String
  show𝔽 = showℕ ∘ 𝔽.toℕ

  show𝕍 : {A : Set ℓ} → (A → String) → Vec A n → String
  show𝕍 showA 𝕍.[] = printf "[]"
  show𝕍 {_} {_} {A} showA as@(_ 𝕍.∷ _) = go "[" as
    where go : String → Vec A (ℕ.suc n) → String
          go acc (a 𝕍.∷ 𝕍.[]) = printf "%s%s]" acc (showA a)
          go acc (a 𝕍.∷ bs@(_ 𝕍.∷ _)) = go (printf "%s%s, " acc (showA a)) bs

  show𝕃 : {A : Set ℓ} → (A → String) → List A → String
  show𝕃 {_} {A} showA = go "["
    where go : String → List A → String
          go acc [] = printf "%s]" acc
          go acc (a ∷ []) = printf "%s%s]" acc (showA a)
          go acc (a ∷ bs@(_ ∷ _)) = go (printf "%s%s, " acc (showA a)) bs

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

record SourceLocation : Set where
  constructor _,_
  field
    filename : String
    offset : ℕ

showSourceLocation : SourceLocation → String
showSourceLocation (fn , i) = printf "%s:%i" fn (+ i)

module Parser (value : Value ℓ₀ ℓ₁) where
  open Value value renaming (Carrier to V)

  data Effect : Set ℓ₀ where
    noop : Effect
    input : Effect
    output : Effect
    op : (V → V) → Effect
    pointer : (ℤ → ℤ) → Effect
    cond : (V → Bool) → Effect

  showEffect : Effect → String
  showEffect noop = "noop"
  showEffect input = "input"
  showEffect output = "output"
  showEffect (op _) = "op"
  showEffect (pointer _) = "pointer"
  showEffect (cond _) = "cond"

  module _ n where
    data Error : Set where
      unmatched : Char → Error
      unimplemented : Error

    data Token : Set ℓ₀ where
      inc : SourceLocation → Token
      dec : SourceLocation → Token
      left : SourceLocation → Token
      right : SourceLocation → Token
      input : SourceLocation → Token
      output : SourceLocation → Token
      jz : Fin n → SourceLocation → Token
      jnz : Fin n → SourceLocation → Token
      comment : Char → SourceLocation → Token

    showToken : Token → String
    showToken (inc l) = printf "inc (%s)" (showSourceLocation l)
    showToken (dec l) = printf "dec (%s)" (showSourceLocation l)
    showToken (left l) = printf "left (%s)" (showSourceLocation l)
    showToken (right l) = printf "right (%s)" (showSourceLocation l)
    showToken (input l) = printf "input (%s)" (showSourceLocation l)
    showToken (output l) = printf "output (%s)" (showSourceLocation l)
    showToken (jz i l) = printf "jz(%i) (%s)" (+ (𝔽.toℕ i)) (showSourceLocation l)
    showToken (jnz i l) = printf "jnz(%i) (%s)" (+ (𝔽.toℕ i)) (showSourceLocation l)
    showToken (comment c l) = printf "%c (%s)" c (showSourceLocation l)

    token : Vec Char n → (Char × Fin n × SourceLocation) → Error ⊎ Token
    token cs ('+' , _ , l) = inj₂ (inc l)
    token cs ('-' , _ , l) = inj₂ (dec l)
    token cs ('<' , _ , l) = inj₂ (left l)
    token cs ('>' , _ , l) = inj₂ (right l)
    token cs (',' , _ , l) = inj₂ (input l)
    token cs ('.' , _ , l) = inj₂ (output l)
    token cs ('[' , i , l) with jz | unmatched '['
    ... | J | E rewrite proj₂ (𝕌.excSplitℕ i) =
      𝕌.match 𝕌.square (𝕍.drop (𝔽.toℕ i) cs) |>
        𝕄.maybe′ (λ j → inj₂ $ J (𝔽.raise _ j) l) (inj₁ E)
    token cs (']' , i , l) with jnz | unmatched ']' | 𝕌.incSplitℕ i
    ... | J | E | (k , P) rewrite P =
      𝕌.match (𝕌.flip 𝕌.square) (𝕍.reverse $ 𝕍.take _ cs) |>
        𝕄.maybe′ (inj₂ ∘ flip J l ∘ go) (inj₁ E)
        where go : Fin (ℕ.suc (𝔽.toℕ i)) → Fin (ℕ.suc (𝔽.toℕ i ℕ.+ k))
              go j with 𝔽.inject+ (𝔽.toℕ j) ((𝔽.toℕ i) 𝔽.ℕ- j)
              ... | l rewrite ℕᵖ.m∸n+n≡m (𝕌.toℕ-≤ j) = 𝔽.inject+ k l
    token cs (c , _ , l) = inj₂ $ comment c l

    tokenize : String → Vec Char n -> Error ⊎ Vec Token n
    tokenize fn cs = M.sequenceA $ 𝕍.map (token cs) src
      where module M = 𝕍ᶜ.TraversableA {ℓ₀} {n} (⊎.applicative Error ℓ₀)
            src = 𝕍.zip cs $ 𝕍.map (λ i → i , fn , 𝔽.toℕ i) $ 𝕍.tabulate id

    L = ⊤ ⊎ Fin n

    showLabel : L → String
    showLabel (inj₁ tt) = "∙"
    showLabel (inj₂ i) = show𝔽 i

    terminal : L
    terminal = inj₁ tt

    initial : L
    initial = inj₁ tt

    record Edge : Set ℓ₀ where
      field
        base target : L
        effect : Effect
        source : Maybe Token

    showEdge : Edge → String
    showEdge record { base = b ; target = t ; effect = e ; source = just k} =
      printf "%s→%s %s %s" (showLabel b) (showLabel t) (showEffect e) (showToken k)
    showEdge record { base = b ; target = t ; effect = e ; source = nothing } =
      printf "%s→%s %s" (showLabel b) (showLabel t) (showEffect e)

    private
      mk : Token → Fin n → Effect → Edge
      mk t b e with n ≟ℕ ℕ.suc (𝔽.toℕ b)
      ... | yes _ = record { base = inj₂ b ; target = terminal ; effect = e; source = just t }
      ... | no P = record { base = inj₂ b ; target = inj₂ $ 𝔽.lower₁ (𝔽.suc b) P; effect = e; source = just t }

    interpretToken : Token → Fin n → List Edge
    interpretToken t@(inc _) b = mk t b (op suc) ∷ []
    interpretToken t@(dec _) b = mk t b (op pred) ∷ []
    interpretToken t@(left _) b = mk t b (pointer ℤ.pred) ∷ []
    interpretToken t@(right _) b = mk t b (pointer ℤ.suc) ∷ []
    interpretToken t@(input _) b = mk t b input ∷ []
    interpretToken t@(output _) b = mk t b output ∷ []
    interpretToken t@(comment _ _) b = mk t b noop ∷ []
    interpretToken t@(jz T _) b = record (mk t b $ cond $ λ v → ⌊ v ≈?0 ⌋) { target = inj₂ T } ∷ mk t b noop ∷ []
    interpretToken t@(jnz T _) b = record (mk t b $ cond $ λ v → not ⌊ v ≈?0 ⌋) { target = inj₂ T } ∷ mk t b noop ∷ []

    record Graph : Set ℓ₀ where
      field
        edges : L → List Edge

    labels : Vec L (ℕ.suc n)
    labels = initial 𝕍.∷ 𝕍.tabulate inj₂

  graph : Vec (Token n) n → Graph n
  graph {𝔽.0F} ts = record { edges = λ _ → record { base = initial _ ; target = terminal _ ; effect = noop ; source = nothing } ∷ [] }
  graph {ℕ.suc n} ts = record { edges = edges }
    where es = 𝕍.zip ts (𝕍.tabulate id) |> 𝕍.map λ { (t , b) → interpretToken _ t b }
          edges : L (ℕ.suc n) → List (Edge (ℕ.suc n))
          edges (inj₁ _) = record { base = initial _ ; target = inj₂ 0F ; effect = noop ; source = nothing } ∷ []
          edges (inj₂ i) = 𝕍.lookup es i

  showGraph : Graph n → String
  showGraph {n} g = goG "{" $ labels n
    where goL : L n → String
          goL = show𝕃 (showEdge _) ∘ Graph.edges g
          goG : String → Vec (L n) m → String
          goG acc 𝕍.[] = printf "%s}" acc
          goG acc (l 𝕍.∷ 𝕍.[]) = printf "%s%s: %s}" acc (showLabel _ l) (goL l)
          goG acc (l 𝕍.∷ ls@(_ 𝕍.∷ _)) =
            goG (printf "%s%s: %s, " acc (showLabel _ l) (goL l)) ls

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

  runAction : Settings → IO _
  runAction s with Settings.action s
  runAction s | debugLexer = do
    let fn = (Settings.programFilename s)
    raw ← readFiniteFile fn
    ts ← handleParserError $ Parser.tokenize integer _ fn (𝕊.toVec raw)
    run ∘ sequence′ $ 𝕃ᶜ.map (putStrLn ∘ Parser.showToken _ _) (𝕃ᶜ.fromList $ 𝕍.toList ts)
  runAction s | debugParser = do
    let fn = (Settings.programFilename s)
    raw ← readFiniteFile fn
    ts ← handleParserError $ Parser.tokenize integer _ fn (𝕊.toVec raw)
    let g = Parser.graph integer ts
    run (putStrLn $ Parser.showGraph _ g) >>= return ∘ lift
  runAction s | usageAction = usage nothing

  main = do
    s ← Unix.getArgs >>= parseArgs
    runAction s
