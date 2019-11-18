module bf.Interpreter where

open import Codata.Musical.Colist as 𝕃ᶜ using (Colist; _∷_; [])
open import Codata.Musical.Notation using (♯_; ♭)
open import Data.Bool using (Bool; true; false; not)
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.List using (List; _∷_; [])
open import Data.Maybe as 𝕄 using (Maybe; just; nothing)
open import Data.Product as ℙ using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_$_; _∘_)
open import Level using (Lift; lift; _⊔_) renaming (suc to lsuc)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Text.Printf using (printf)

record Tape {ℓ} (V : Set ℓ) : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    get : Carrier → ℤ → Maybe V
    set : Carrier → ℤ → V → Carrier
    empty : Carrier

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

module Mk {ℓ₀} {ℓ₁} (value : Value ℓ₀ ℓ₁) (Tape : Tape (Value.Carrier value)) where
  open Value value renaming (Carrier to V)
  open Tape Tape renaming (Carrier to T)
  open import bf.Parser as Parser using (Graph; Label; Edge)

  record State : Set ℓ₀ where
    field
      tape : T
      pointer : ℤ
      program : Σ[ g ∈ Graph ] Label (Graph.size g)

  initial : Graph → State
  initial g = record { tape = empty ; pointer = + 0 ; program = g , Parser.initial }

  module _ (s : State) where
    private
      g = (proj₁ $ State.program s)
      l = (proj₂ $ State.program s)
      size = Graph.size g

    goto : Label size → State
    goto l = record s { program = g , l }

    showState : String
    showState = printf "{ program = %s , %s }" (Parser.showGraph g) (Parser.showLabel l)

  op : Parser.Op → V → V
  op Parser.inc = suc
  op Parser.dec = pred

  ptrArith : Parser.PtrArith → ℤ → ℤ
  ptrArith Parser.inc = ℤ.suc
  ptrArith Parser.dec = ℤ.pred

  cond : Parser.Cond → V → Bool
  cond Parser.z v = ⌊ v ≈?0 ⌋
  cond Parser.nz v = not ⌊ v ≈?0 ⌋

  data EOFBehavior : Set ℓ₀ where
    writeValue : V → EOFBehavior
    writeDefault : EOFBehavior
    leaveUnmodified : EOFBehavior

  step : EOFBehavior → State → Colist V → State × Colist V × Maybe V
  step eof s input = go eof (Graph.edges g (proj₂ $ State.program s)) input
    where g = proj₁ (State.program s)
          tape = State.tape s
          p = State.pointer s
          go : EOFBehavior → List (Edge (Graph.size g)) → Colist V → State × Colist V × Maybe V
          go eof [] input = s , input , nothing
          go eof (record { target = t ; effect = Parser.noop } ∷ _) input = goto s t , input , nothing
          go eof (record { target = t ; effect = Parser.input } ∷ _) [] with eof
          go eof (record { target = t ; effect = Parser.input } ∷ _) [] | writeDefault =
            goto record s { tape = set tape p (default nothing) } t , input , nothing
          go eof (record { target = t ; effect = Parser.input } ∷ _) [] | writeValue v =
            goto record s { tape = set tape p v } t , input , nothing
          go eof (record { target = t ; effect = Parser.input } ∷ _) [] | leaveUnmodified =
            goto s t , input , nothing
          go eof (record { target = t ; effect = Parser.input } ∷ _) (v ∷ input) =
            goto record s { tape = set tape p v } t , ♭ input , nothing
          go eof (record { target = t ; effect = Parser.output } ∷ _) input =
            goto s t , input , just (default $ get tape p)
          go eof (record { target = t ; effect = Parser.op o } ∷ _) input =
            goto record s { tape = set tape p ∘ op o ∘ default $ get tape p } t , input , nothing
          go eof (record { target = t ; effect = Parser.pointer pa } ∷ _) input =
            goto record s { pointer = ptrArith pa p } t , input , nothing
          go eof (record { target = t ; effect = Parser.cond c } ∷ es) input with cond c ∘ default $ get tape p
          go eof (record { target = t ; effect = Parser.cond c } ∷ es) input | false = go eof es input
          go eof (record { target = t ; effect = Parser.cond c } ∷ es) input | true = goto s t , input , nothing

  terminated? : State → Bool
  terminated? record { program = _ , Label.initial } = false
  terminated? record { program = _ , Label.terminal } = true
  terminated? record { program = _ , Label.index _ } = false

  eval : EOFBehavior → State → Colist V → Colist (State × Colist V × Maybe V)
  eval eof s input with terminated? s
  eval eof s input | false = let hd@(s , input , _) = step eof s input in hd ∷ ♯ eval eof s input
  eval eof s input | true = []

  {-# TERMINATING #-}
  run : EOFBehavior → Graph → Colist V → Colist V
  run eof g input = flatten ∘ 𝕃ᶜ.map (λ { ( _ , _ , output ) → output }) $ eval eof (initial g) input
    where flatten : Colist (Maybe V) → Colist V
          flatten [] = []
          flatten (nothing ∷ vs) = flatten (♭ vs)
          flatten (just v ∷ vs) = v ∷ ♯ flatten (♭ vs)

