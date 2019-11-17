module bf.Interpreter where

open import Category.Monad using (RawMonad)
open import Data.Bool using (Bool; true; false; not)
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.List using (List; _∷_; [])
open import Data.Maybe as 𝕄 using (Maybe)
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

record Tape {ℓ₀} (V : Set ℓ₀) (F : ∀ {ℓ} → Set ℓ → Set ℓ) : Set ℓ₀ where
  field
    get : ℤ → F (Maybe V)
    set : ℤ → V → F (Lift ℓ₀ ⊤)

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

module Mk {ℓ₀} {ℓ₁}
  (value : Value ℓ₀ ℓ₁)
  {f : ∀ {ℓ} → Set ℓ → Set ℓ} (F : ∀ {ℓ} → RawMonad {ℓ} f) where
  open Value value renaming (Carrier to V)
  open import bf.Parser as Parser using (Graph; Label; Edge)
  open RawMonad {ℓ₀} F

  record State : Set ℓ₀ where
    field
      tape : Tape V f
      pointer : ℤ
      program : Σ[ g ∈ Graph ] Label (Graph.size g)

  initial : Graph → Tape V f → State
  initial g t = record { tape = t ; pointer = + 0 ; program = g , Parser.initial _ }

  module _ (s : State) where
    private
      g = (proj₁ $ State.program s)
      l = (proj₂ $ State.program s)
      size = Graph.size g

    goto : Label size → State
    goto l = record s { program = g , l }

    showState : String
    showState = printf "{ program = %s , %s }" (Parser.showGraph g) (Parser.showLabel l)

  record IOHandlers : Set ℓ₀ where
    field
      input : ⊤ → f V
      output : V → f (Lift ℓ₀ ⊤)

  op : Parser.Op → V → V
  op Parser.inc = suc
  op Parser.dec = pred

  ptrArith : Parser.PtrArith → ℤ → ℤ
  ptrArith Parser.inc = ℤ.suc
  ptrArith Parser.dec = ℤ.pred

  cond : Parser.Cond → V → Bool
  cond Parser.z v = ⌊ v ≈?0 ⌋
  cond Parser.nz v = not ⌊ v ≈?0 ⌋

  step : IOHandlers → State → f State
  step io s = go (Graph.edges g (proj₂ $ State.program s))
    where g = proj₁ (State.program s)
          size = Graph.size g
          go : List (Edge size) → f State
          go [] = return s
          go (e ∷ _) with Edge.effect e
          go (e ∷ _) | Parser.noop = return (goto s $ Edge.target e)
          go (e ∷ _) | Parser.input =
            IOHandlers.input io tt >>= Tape.set (State.tape s) (State.pointer s) >>
            return (goto s $ Edge.target e)
          go (e ∷ _) | Parser.output =
            default <$> Tape.get (State.tape s) (State.pointer s) >>= IOHandlers.output io >>
            return (goto s $ Edge.target e)
          go (e ∷ _) | Parser.op o =
            default <$> Tape.get (State.tape s) (State.pointer s) >>=
            Tape.set (State.tape s) (State.pointer s) ∘ op o >>
            return (goto s (Edge.target e))
          go (e ∷ _) | Parser.pointer p =
            return (goto record s { pointer = ptrArith p $ State.pointer s } $ Edge.target e)
          go (e ∷ es) | Parser.cond c = do
            lift true ← lift ∘ cond c ∘ default <$> Tape.get (State.tape s) (State.pointer s)
              where lift false → go es
            return (goto s $ Edge.target e)

  {-# NON_TERMINATING #-}
  run : IOHandlers → State → f State
  run io s = step io s >>= halt?
    where halt? : State → f State
          halt? s′ with proj₂ $ State.program s′
          halt? s′ | inj₁ tt = return s′
          halt? s′ | inj₂ y = run io s′
