module bf where

import util as 𝕌

open import Data.Bool using (Bool; not; true)
open import Data.Maybe as 𝕄 using (Maybe; nothing; just)
open import Data.List as 𝕃 using (List; []; _∷_)
open import Data.Char using (Char)
open import Data.Nat as ℕ using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Show renaming (show to showℕ)
import Data.Nat.Properties as ℕᵖ
open import Data.Vec as 𝕍 using (Vec; []; _∷_)
import Data.Vec.Categorical as 𝕍ᶜ
open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Integer as ℤ using (ℤ; +_) renaming (_≟_ to _≟ℤ_)
open import Data.Unit using (⊤; tt)
open import Function using (_|>_; _$_; flip; id; _∘_)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
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
  show𝕍 showA [] = printf "[]"
  show𝕍 {_} {_} {A} showA as@(_ ∷ _) = go "[" as
    where go : String → Vec A (ℕ.suc n) → String
          go acc (a ∷ []) = printf "%s%s]" acc (showA a)
          go acc (a ∷ bs@(_ ∷ _)) = go (printf "%s%s, " acc (showA a)) bs

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

module Lexer where
  data Token : Set where
    inc : SourceLocation → Token
    dec : SourceLocation → Token
    left : SourceLocation → Token
    right : SourceLocation → Token
    input : SourceLocation → Token
    output : SourceLocation → Token
    jz : SourceLocation → Token
    jnz : SourceLocation → Token
    comment : Char → SourceLocation → Token

  showToken : Token → String
  showToken (inc l) = printf "inc (%s)" (showSourceLocation l)
  showToken (dec l) = printf "dec (%s)" (showSourceLocation l)
  showToken (left l) = printf "left (%s)" (showSourceLocation l)
  showToken (right l) = printf "right (%s)" (showSourceLocation l)
  showToken (input l) = printf "input (%s)" (showSourceLocation l)
  showToken (output l) = printf "output (%s)" (showSourceLocation l)
  showToken (jz l) = printf "jz (%s)" (showSourceLocation l)
  showToken (jnz l) = printf "jnz (%s)" (showSourceLocation l)
  showToken (comment c l) = printf "%c (%s)" c (showSourceLocation l)

  token : Char × SourceLocation → Token
  token ('+' , l) = inc l
  token ('-' , l) = dec l
  token ('<' , l) = left l
  token ('>' , l) = right l
  token (',' , l) = input l
  token ('.' , l) = output l
  token ('[' , l) = jz l
  token (']' , l) = jnz l
  token (c , l) = comment c l

  tokenize : String → Vec Char n -> Vec Token n
  tokenize fn cs = 𝕍.map token $ 𝕍.zip cs $ 𝕍.map (λ i → fn , 𝔽.toℕ i) $ 𝕍.tabulate id

module Parser (value : Value ℓ₀ ℓ₁) where
  open Value value renaming (Carrier to V)
  open Lexer

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

  data Error : Set where
    unmatched : Token → Error
    unimplemented : Error

  Label : ℕ → Set
  Label n = ⊤ ⊎ Fin n

  showLabel : Label n → String
  showLabel (inj₁ tt) = "∙"
  showLabel (inj₂ i) = show𝔽 i

  record Edge n : Set ℓ₀ where
    field
      base target : Label n
      effect : Effect
      source : Maybe Token

  showEdge : Edge n → String
  showEdge record { base = b ; target = t ; effect = e ; source = just k} =
    printf "%s→%s %s %s" (showLabel b) (showLabel t) (showEffect e) (showToken k)
  showEdge record { base = b ; target = t ; effect = e ; source = nothing } =
    printf "%s→%s %s" (showLabel b) (showLabel t) (showEffect e)

  record Graph : Set ℓ₀ where
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
    interpretToken _ t@(inc _) b = inj₂ $ mk t b (op suc) ∷ []
    interpretToken _ t@(dec _) b = inj₂ $ mk t b (op pred) ∷ []
    interpretToken _ t@(left _) b = inj₂ $ mk t b (pointer ℤ.pred) ∷ []
    interpretToken _ t@(right _) b = inj₂ $ mk t b (pointer ℤ.suc) ∷ []
    interpretToken _ t@(input _) b = inj₂ $ mk t b input ∷ []
    interpretToken _ t@(output _) b = inj₂ $ mk t b output ∷ []
    interpretToken _ t@(comment _ _) b = inj₂ $ mk t b noop ∷ []
    interpretToken raw t@(jz _) b with mk t b
    ... | mk′ rewrite proj₂ (𝕌.excSplitℕ b) =
      𝕌.match brackets (𝕍.drop (𝔽.toℕ b) raw) |> 𝕄.maybe′ f (inj₁ (unmatched t))
        where f = λ j → inj₂ $ record (mk′ $ cond $ (λ v → ⌊ v ≈?0 ⌋)) { target = inj₂ (𝔽.raise _ j) } ∷ mk′ noop ∷ []
    interpretToken raw t@(jnz _) b with mk t b
    ... | mk′ rewrite proj₂ (𝕌.incSplitℕ b) =
      𝕌.match (𝕌.flip brackets) (𝕍.reverse $ 𝕍.take _ raw) |> 𝕄.maybe′ f (inj₁ $ unmatched t)
        where go : ∀ k → Fin (ℕ.suc (𝔽.toℕ b)) → Fin (ℕ.suc (𝔽.toℕ b ℕ.+ k))
              go k j with 𝔽.inject+ (𝔽.toℕ j) (𝔽.toℕ b 𝔽.ℕ- j)
              ... | l rewrite ℕᵖ.m∸n+n≡m (𝕌.toℕ-≤ j) = 𝔽.inject+ k l
              f = λ j → inj₂ $ record (mk′ $ cond $ λ v → not ⌊ v ≈?0 ⌋) { target = inj₂ $ go _ j } ∷ mk′ noop ∷ []

  module _ (g : Graph) where
    private
      s = Graph.size g

    labels : Vec (Label s) (ℕ.suc s)
    labels = initial s ∷ 𝕍.tabulate inj₂

  graph : Vec Token n → Error ⊎ Graph
  graph {𝔽.0F} ts = inj₂ $ record { size = 0 ; edges = λ _ → record { base = initial _ ; target = terminal _ ; effect = noop ; source = nothing } ∷ [] }
  graph {n@(ℕ.suc _)} ts = map₂ (λ es → record { size = n ; edges = edges es }) $
    M.sequenceA $ 𝕍.zip ts (𝕍.tabulate id) |> 𝕍.map λ { (t , b) → interpretToken n ts t b }
      where module M = 𝕍ᶜ.TraversableA {ℓ₀} {n} (⊎.applicative Error ℓ₀)
            edges : Vec (List (Edge n)) n → Label n → List (Edge n)
            edges _ (inj₁ _) = record { base = initial _ ; target = inj₂ 0F ; effect = noop ; source = nothing } ∷ []
            edges es (inj₂ i) = 𝕍.lookup es i

  showGraph : Graph → String
  showGraph g = goG "{" $ (labels g)
    where goL : Label (Graph.size g) → String
          goL = show𝕃 showEdge ∘ Graph.edges g
          goG : String → Vec (Label (Graph.size g)) m → String
          goG acc [] = printf "%s}" acc
          goG acc (l ∷ []) = printf "%s%s: %s}" acc (showLabel l) (goL l)
          goG acc (l ∷ ls@(_ ∷ _)) =
            goG (printf "%s%s: %s, " acc (showLabel l) (goL l)) ls

module Interpreter (value : Value ℓ₀ ℓ₁) (F : ∀ {ℓ} → Set ℓ → Set ℓ) where
  open Value value renaming (Carrier to V)
  open Parser value using (Graph; Label)

  record State ℓ : Set (lsuc (ℓ ⊔ ℓ₀)) where
    field
      tape : Tape ℓ V F
      pointer : ℤ
      program : ∃[ n ] Label n × Graph

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
          go (s ∷ []) a _ | no _ | no _ = return record { action = a ; programFilename = s }
          go (s ∷ x ∷ cs) a obf | no ¬p | no ¬p₁ = usage nothing

  handleParserError : {v : Value ℓ ℓ₀} {a : Set} → Parser.Error v ⊎ a → IO a
  handleParserError (inj₁ (Parser.unmatched t)) = Unix.die $ printf "unmatched %s" (Lexer.showToken t)
  handleParserError (inj₁ Parser.unimplemented) = Unix.die $ printf "unimplemented"
  handleParserError (inj₂ a) = return a

  runAction : Settings → IO _
  runAction s with Settings.action s
  runAction s | debugLexer = do
    let fn = (Settings.programFilename s)
    raw ← readFiniteFile fn
    let ts = Lexer.tokenize fn (𝕊.toVec raw)
    run ∘ sequence′ $ 𝕃ᶜ.map (putStrLn ∘ Lexer.showToken) (𝕃ᶜ.fromList $ 𝕍.toList ts)
  runAction s | debugParser = do
    let fn = (Settings.programFilename s)
    raw ← readFiniteFile fn
    g ← handleParserError $ Parser.graph integer $ Lexer.tokenize fn (𝕊.toVec raw)
    run (putStrLn $ Parser.showGraph _ g) >>= return ∘ lift
  runAction s | usageAction = usage nothing

  main = Unix.getArgs >>= parseArgs >>= runAction
