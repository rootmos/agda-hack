module Unix where

open import Data.List using (List)
open import Data.String using (String)
open import IO.Primitive using (IO)
open import Data.Unit using (⊤)
open import Data.Integer using (ℤ)

{-# FOREIGN GHC import qualified System.Environment #-}
{-# FOREIGN GHC import qualified System.Exit as E #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}

postulate
  getArgs : IO (List String)

{-# COMPILE GHC getArgs = fmap (fmap T.pack) System.Environment.getArgs #-}

data ExitCode : Set where
  success : ExitCode
  failure : ℤ → ExitCode

{-# FOREIGN GHC
  data ExitCode' = ExitSuccess' | ExitFailure' Integer

  convertExitCode :: ExitCode' -> E.ExitCode
  convertExitCode ExitSuccess' = E.ExitSuccess
  convertExitCode (ExitFailure' i) = E.ExitFailure (fromIntegral i)
#-}
{-# COMPILE GHC ExitCode = data ExitCode' (ExitSuccess' | ExitFailure') #-}

postulate
  exit : {a : Set} → ExitCode → IO a
  die : {a : Set} → String → IO a

{-# COMPILE GHC exit = \ _ ec -> E.exitWith (convertExitCode ec) #-}
{-# COMPILE GHC die = \ _ msg -> E.die (T.unpack msg) #-}
