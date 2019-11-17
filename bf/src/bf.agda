module bf where

import Unix

open import bf.Lexer as Lexer using (showToken)
import bf.Parser as Parser
import bf.Interpreter as Interpreter

open import Category.Monad using (RawMonad)
import Codata.Musical.Colist as 𝕃ᶜ
open import Data.AVL.Map as Map using (Map)
open import Data.Char as ℂ using (Char)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]) renaming (_≟_ to _≟ℤ_)
import Data.Integer.Properties as ℤᵖ
open import Data.List as 𝕃 using (List; []; _∷_)
open import Data.Maybe as 𝕄 using (Maybe; nothing; just)
open import Data.String as 𝕊 using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec as 𝕍 using (Vec; []; _∷_)
open import Data.Product using (_,_)
open import Function using (_|>_; _$_; _∘_)
open import IO using (lift; run; sequence′; putStrLn)
open import IO.Primitive as IO′ using (IO; readFiniteFile)
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

IOMonad : ∀ {ℓ} → RawMonad {ℓ} IO
IOMonad = record { return = IO′.return ; _>>=_ = IO′._>>=_ }
open RawMonad {levelOfType ℤ} IOMonad

module I where
  open Interpreter.Mk integer IOMonad public

  empty : IO (Interpreter.Tape ℤ IO)
  empty = Unix.newIORef (Map.empty ℤᵖ.<-strictTotalOrder) <&> λ r →
    record { get = λ k → Unix.readIORef r <&> Map.lookup _ k
           ; set = λ k v →
             Unix.readIORef r >>= Unix.writeIORef r ∘ Map.insert _ k v <&> lift
           }

  io : IOHandlers
  io = record { input = λ _ → Unix.getChar <&> 𝕄.maybe′ (λ c → + ℂ.toℕ c) (+ 0)
              ; output = λ { (+ n) → lift <$> Unix.putChar (ℂ.fromℕ n)
                           ; -[1+ n ] → Unix.die "cannot print negative values"
                           }
              }

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
    ec ← 𝕄.maybe′ (λ s → run (putStrLn s) >> return (Unix.failure $ + 2 , λ ())) (return Unix.success) s
    p ← Unix.getProgName
    run ∘ putStrLn $ printf "Usage: %s [OPTION]... FILE" p
    run ∘ putStrLn $        "Interpret the BrainFuck program in FILE"
    run ∘ putStrLn $        ""
    run ∘ putStrLn $        " --lexer   run lexer and output tokens"
    run ∘ putStrLn $        " --parser  run parser and output the parsed program"
    Unix.exit ec

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
    let fn = (Settings.programFilename s)
    raw ← readFiniteFile fn
    let ts = Lexer.tokenize fn (𝕊.toVec raw)
    run ∘ sequence′ $ 𝕃ᶜ.map (putStrLn ∘ showToken) (𝕃ᶜ.fromList $ 𝕍.toList ts)
  runAction s | debugParser = do
    let fn = (Settings.programFilename s)
    raw ← readFiniteFile fn
    g ← handleParserError $ Parser.graph ∘ Lexer.tokenize fn $ 𝕊.toVec raw
    run (putStrLn $ Parser.showGraph g) <&> lift
  runAction s | interpret = do
    let fn = (Settings.programFilename s)
    raw ← readFiniteFile fn
    g ← handleParserError $ Parser.graph ∘ Lexer.tokenize fn $ 𝕊.toVec raw
    (I.run I.io ∘ I.initial g =<< I.empty) >> return (lift tt)

  main = Unix.getArgs >>= parseArgs >>= runAction
