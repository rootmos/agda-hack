module exit-failure where

open import Category.Monad using (RawMonad)

open import Data.Unit using (⊤)
open import Overture.IO as IO using (IO)
open import Data.Product using (_,_)
open import Data.Integer using (+_)
open import Overture.Unix
import Level

open RawMonad {Level.zero} IO.monad

main : IO ⊤
main = do
  IO.putStrLn "inb4 failure"
  exit (failure (+ 7 , λ ()))
