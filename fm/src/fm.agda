module fm where

open import Function
open import Data.Nat
open import Data.Char
open import Data.List
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Vec using (Vec; fromList)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as M

private
  variable
    n m : ℕ
    A B : Set

data Token (m : ℕ): Set where
  inc : Token m
  left : Token m
  right : Token m
  jz : Token m
  jnz : Token m
  comment : Char -> Token m

token : Char -> Token m
token '+' = inc
token '<' = left
token '>' = right
token '[' = jz
token ']' = jnz
token c = comment c

tokenize : List Char -> List (Token m)
tokenize cs = map token cs

data Term (m : ℕ): Set where
  inc : Term m
  left : Term m
  right : Term m
  jz : n > 0 -> Term m
  jnz : n > 0 -> Term m

parse : List (Token m) -> Maybe (List (Term m))
parse ts = M.map (reverse ∘ proj₁) (foldr (go (fromList ts)) (just ([] , 0)) ts)
  where
    go : Vec (Token m) n -> Token m -> Maybe (List (Term m) × ℕ) -> Maybe (List (Term m) × ℕ)
    go _ _ nothing = nothing
    go _ inc (just (ts , i)) = just (inc ∷ ts , i + 1)
    go _ left (just (ts , i)) = just (left ∷ ts , i + 1)
    go _ right (just (ts , i)) = just (right ∷ ts , i + 1)
    go _ (comment _) (just (ts , i)) = just (ts , i + 1)
    go p jz (just x) = ?
    go p jnz (just x) = ?
