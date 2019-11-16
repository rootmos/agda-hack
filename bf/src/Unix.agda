module Unix where

open import Data.Char using (Char)
open import Data.Integer using (ℤ)
open import Data.List using (List)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import IO.Primitive using (IO)

{-# FOREIGN GHC import qualified System.Environment #-}
{-# FOREIGN GHC import qualified System.Exit as E #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified Data.IORef as R #-}


postulate
  getArgs : IO (List String)
  getChar : IO Char
  putChar : Char → IO ⊤

{-# COMPILE GHC getArgs = fmap (fmap T.pack) System.Environment.getArgs #-}
{-# COMPILE GHC getChar = getChar #-}
{-# COMPILE GHC putChar = putChar #-}

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


postulate
  IORef : (a : Set) → Set
  newIORef : ∀ {a} → a → IO (IORef a)
  readIORef : ∀ {a} → IORef a → IO a
  writeIORef : ∀ {a} → IORef a → a → IO ⊤

{-# COMPILE GHC IORef = type R.IORef #-}
{-# COMPILE GHC newIORef = \ _ -> R.newIORef #-}
{-# COMPILE GHC readIORef = \ _ -> R.readIORef #-}
{-# COMPILE GHC writeIORef = \ _ -> R.writeIORef #-}
