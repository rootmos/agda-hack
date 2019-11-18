module Overture.IO where

open import Category.Monad using (RawMonad)
import IO as StdIO
open import IO.Primitive as IO′ using (readFiniteFile) public
open import Function using (_∘_; _$_)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Codata.Musical.Colist as 𝕃ᶜ using (Colist)
open import Level using (Lift) renaming (suc to lsuc)

IO = IO′.IO

-- reexports
putStrLn = StdIO.run ∘ StdIO.putStrLn
putStrLnᶜ = StdIO.run ∘ StdIO.putStrLn∞
getContents = StdIO.run StdIO.getContents

sequence′ : ∀ {ℓ} {a : Set ℓ} → Colist (IO a) → IO (Lift ℓ ⊤)
sequence′ = StdIO.run ∘ StdIO.sequence′ ∘ 𝕃ᶜ.map StdIO.lift

monad : ∀ {ℓ} → RawMonad {ℓ} IO
monad = record { return = IO′.return ; _>>=_ = IO′._>>=_ }
