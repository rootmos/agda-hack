module bf.Lexer where

open import Data.Char using (Char)
import Data.Fin as 𝔽
open import Data.Integer using (+_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Vec as 𝕍 using (Vec)
open import Function using (_$_; id)
open import Text.Printf using (printf)

record SourceLocation : Set where
  constructor _,_
  field
    filename : String
    offset : ℕ

showSourceLocation : SourceLocation → String
showSourceLocation (fn , i) = printf "%s:%i" fn (+ i)

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

tokenize : ∀ {n} String → Vec Char n -> Vec Token n
tokenize fn cs = 𝕍.map token $ 𝕍.zip cs $ 𝕍.map (λ i → fn , 𝔽.toℕ i) $ 𝕍.tabulate id
