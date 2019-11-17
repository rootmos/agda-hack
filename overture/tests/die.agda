module die where

open import Data.Unit using (⊤)
open import Overture.IO as IO using (IO)
open import Overture.Unix

main : IO ⊤
main = die "whoops!"
