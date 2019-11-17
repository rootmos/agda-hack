module exit-success where

open import Category.Monad using (RawMonad)

open import Data.Unit using (⊤)
open import Overture.IO as IO using (IO)
open import Overture.Unix
import Level

open RawMonad {Level.zero} IO.monad

main : IO ⊤
main = do
  IO.putStrLn "inb4 success"
  exit success
