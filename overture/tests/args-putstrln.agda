module args-putstrln where

open import Data.Unit using (⊤)
open import Overture.IO as IO using (IO)
open import Overture.Unix

open import Category.Monad using (RawMonad)
open import Data.List using ([]; _∷_)
import Level

open RawMonad {Level.zero} IO.monad

main : IO ⊤
main = getArgs >>= λ { (s ∷ []) → IO.putStrLn s ; _ → die "wrong number of arguments" }
