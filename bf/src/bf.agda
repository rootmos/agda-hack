module bf where

open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe)
open import Data.List as 𝕃 using (List)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Level using (Level; _⊔_; suc; Lift)
open import Data.Integer using (ℤ)
open import Data.Unit using (⊤)

private
  variable
    n m : ℕ
    i j k l : ℤ
    ℓ ℓ₀ ℓ₁ : Level

data Token : Set where
  inc : Token
  dec : Token
  left : Token
  right : Token
  input : Token
  output : Token
  jz : Token
  jnz : Token
  comment : Char -> Token

token : Char -> Token
token '+' = inc
token '-' = dec
token '<' = left
token '>' = right
token ',' = input
token '.' = output
token '[' = jz
token ']' = jnz
token c = comment c

tokenize : List Char -> List Token
tokenize cs = 𝕃.map token cs

record Tape ℓ (V : Set ℓ₀) (F : Set ℓ₀ → Set ℓ₀) : Set (ℓ₀ ⊔ suc ℓ) where
  field
    Carrier : Set ℓ
    get : Carrier → ℤ → F (Maybe V)
    set : Carrier → ℤ → V → F (Lift ℓ₀ ⊤)

module Interpreter (V : Set ℓ₀) (F : Set ℓ₀ → Set ℓ₀) where
  data Effect : Set ℓ₀

  record Edge : Set ℓ₀ where
    inductive
    field
      condition : Maybe (Maybe V → Bool)
      effect : Effect

  record Node : Set ℓ₀ where
    inductive
    field
      exit : List Edge
      sourceLocation : ℕ

  record State : Set (suc (ℓ ⊔ ℓ₀)) where
    field
      tape : Tape ℓ V F
      pointer : ℤ
      program : Node

  data Effect where
    halt : Effect
    jump : Node → Effect
    input : Node → Effect
    output : Node → Effect
    op : (Maybe V → V) → Node → Effect
    pointer : (ℤ → ℤ) → Node → Effect
