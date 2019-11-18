module bf where

import Overture.Unix as Unix
open import Overture.IO as IO
import Overture.IORef as IORef

open import bf.Lexer as Lexer using (showToken)
import bf.Parser as Parser
import bf.Interpreter as Interpreter

open import Category.Monad using (RawMonad)
open import Codata.Musical.Colist as 𝕃ᶜ using (Colist; []; _∷_)
open import Codata.Musical.Notation
open import Data.AVL.Map as Map using (Map)
open import Data.Char as ℂ using (Char)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]) renaming (_≟_ to _≟ℤ_)
import Data.Integer.Properties as ℤᵖ
open import Data.List as 𝕃 using (List; []; _∷_)
open import Data.Maybe as 𝕄 using (Maybe; nothing; just)
open import Data.String as 𝕊 using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂; from-inj₂)
open import Data.Unit using (⊤)
open import Data.Vec as 𝕍 using (Vec; []; _∷_)
open import Data.Product using (_,_)
open import Function using (_|>_; _$_; _∘_; id)
open import Level using (Level; Lift; lift; levelOfType)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)
open import Text.Printf using (printf)

integer : Interpreter.Value _ _
integer = record { Carrier = ℤ
                 ; _≈_ = _≡_
                 ; 0# = + 0
                 ; _≈?0 = λ v → v ≟ℤ + 0
                 ; suc = ℤ.suc
                 ; pred = ℤ.pred
                 }

tape : Interpreter.Tape ℤ
tape = record { Carrier = _
              ; get = λ t k → Map.lookup _ k t
              ; set = λ t k v → Map.insert _ k v t
              ; empty = Map.empty ℤᵖ.<-strictTotalOrder
              }

module I = Interpreter.Mk integer tape

open RawMonad {levelOfType ℤ} IO.monad

runIO : Parser.Graph → IO _
runIO g = sequence′ ∘ 𝕃ᶜ.map output ∘ I.run I.writeDefault g =<< 𝕃ᶜ.map (λ c → + ℂ.toℕ c) <$> getContents
    where output : ℤ → IO ⊤
          output (+ n) = Unix.putChar (ℂ.fromℕ n)
          output -[1+ n ] = Unix.die "cannot print negative values"

module cli where
  data Action : Set where
    debugLexer : Action
    debugParser : Action
    usageAction : Action
    interpret : Action

  record Settings : Set where
    field
      action : Action
      programFilename : String

  usage : {a : Set} → Maybe String → IO a
  usage s = do
    ec ← 𝕄.maybe′ putStrLn (return _) s
    p ← Unix.getProgName
    putStrLn $ printf "Usage: %s [OPTION]... FILE" p
    putStrLn $        "Interpret the BrainFuck program in FILE"
    putStrLn $        ""
    putStrLn $        " --lexer   run lexer and output tokens"
    putStrLn $        " --parser  run parser and output the parsed program"
    Unix.exit $ 𝕄.maybe′ (λ _ → Unix.failure $ + 2 , λ ()) Unix.success s

  parseArgs : List String → IO Settings
  parseArgs cs = go cs interpret nothing
    where go : List String → Action → Maybe String → IO Settings
          go [] a _ = usage nothing
          go (s ∷ cs) a _ with s 𝕊.≟ "--lexer"
          go (s ∷ cs) _ obf | yes _ = go cs debugLexer obf
          go (s ∷ cs) a _ | no _ with s 𝕊.≟ "--parser"
          go (s ∷ cs) a obf | no _ | yes _ = go cs debugParser obf
          go (s ∷ []) a _ | no _ | no _ = return record { action = a ; programFilename = s }
          go (s ∷ _ ∷ _) _ _ | no _ | no _ = usage $ just "trailing positional argument(s)"

  handleParserError : {a : Set} → Parser.Error ⊎ a → IO a
  handleParserError (inj₁ (Parser.unmatched t)) = Unix.die $ printf "unmatched %s" (showToken t)
  handleParserError (inj₁ Parser.unimplemented) = Unix.die $ printf "unimplemented"
  handleParserError (inj₂ a) = return a

  runAction : Settings → IO _
  runAction s with Settings.action s
  runAction s | usageAction = usage nothing
  runAction s | debugLexer = do
    let fn = Settings.programFilename s
    raw ← IO.readFiniteFile fn
    let ts = Lexer.tokenize fn (𝕊.toVec raw)
    sequence′ $ 𝕃ᶜ.map (putStrLn ∘ showToken) (𝕃ᶜ.fromList $ 𝕍.toList ts)
  runAction s | debugParser = do
    let fn = Settings.programFilename s
    raw ← readFiniteFile fn
    g ← handleParserError $ Parser.graph ∘ Lexer.tokenize fn $ 𝕊.toVec raw
    (putStrLn $ Parser.showGraph g) <&> lift
  runAction s | interpret = do
    let fn = Settings.programFilename s
    raw ← readFiniteFile fn
    g ← handleParserError $ Parser.graph ∘ Lexer.tokenize fn $ 𝕊.toVec raw
    runIO g

  main = Unix.getArgs >>= parseArgs >>= runAction

module Proofs where
  module Empty where
    empty = I.run I.writeDefault $ from-inj₂ $ Parser.graph ∘ Lexer.tokenize "-" ∘ 𝕊.toVec $ ""

    formal : Colist ℤ → Colist ℤ
    formal _ = []

    proof : empty I.∼ formal
    proof _ = []

  module One where
    one = I.run I.writeDefault $ from-inj₂ $ Parser.graph ∘ Lexer.tokenize "-" ∘ 𝕊.toVec $ ",."

    formal : Colist ℤ → Colist ℤ
    formal [] = + 0 ∷ ♯ []
    formal (i ∷ _) = i ∷ ♯ []

    proof : one I.∼ formal
    proof [] = _ ∷ ♯ []
    proof (_ ∷ _) = _ ∷ ♯ []

  module Two where
    two = I.run I.writeDefault $ from-inj₂ $ Parser.graph ∘ Lexer.tokenize "-" ∘ 𝕊.toVec $ "++."

    formal : Colist ℤ → Colist ℤ
    formal _ = + 2 ∷ ♯ []

    proof : two I.∼ formal
    proof _ = _ ∷ ♯ []
