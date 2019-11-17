module Unix where

open import Data.Char using (Char)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Unit using (⊤)
open import IO.Primitive using (IO; _>>=_; return)
open import Function using (_∘_)
import Foreign.Haskell as ℍ
open import Relation.Binary.PropositionalEquality using (_≢_)

{-# FOREIGN GHC import qualified System.Environment as Env #-}
{-# FOREIGN GHC import qualified System.Exit as E #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified Data.IORef as R #-}
{-# FOREIGN GHC import qualified System.IO.Error as Err #-}
{-# FOREIGN GHC import Control.Exception (catch) #-}
{-# FOREIGN GHC import qualified Data.Bool as B #-}

postulate
  getArgs : IO (List String)
  getProgName : IO String
  putChar : Char → IO ⊤

{-# COMPILE GHC getArgs = fmap (fmap T.pack) Env.getArgs #-}
{-# COMPILE GHC getProgName = fmap T.pack Env.getProgName #-}
{-# COMPILE GHC putChar = putChar #-}

private
  postulate
    getChar′ : IO (ℍ.Maybe Char)

{-# COMPILE GHC getChar′ = catch (Just <$> getChar) (\e -> B.bool (Err.ioError e) (return Nothing) (Err.isEOFError e)) #-}
getChar = getChar′ >>= return ∘ ℍ.fromForeignMaybe

private
  data ExitCode′ : Set where
    success : ExitCode′
    failure : ℤ → ExitCode′

{-# FOREIGN GHC
  data ExitCode'' = ExitSuccess'' | ExitFailure'' Integer

  convertExitCode :: ExitCode'' -> E.ExitCode
  convertExitCode ExitSuccess'' = E.ExitSuccess
  convertExitCode (ExitFailure'' i) = E.ExitFailure (fromIntegral i)
#-}
{-# COMPILE GHC ExitCode′ = data ExitCode'' (ExitSuccess'' | ExitFailure'') #-}

private
  postulate
    exit′ : {a : Set} → ExitCode′ → IO a
{-# COMPILE GHC exit′ = \ _ ec -> E.exitWith (convertExitCode ec) #-}

data ExitCode : Set where
  success : ExitCode
  failure : Σ[ ec ∈ ℤ ] ec ≢ + 0 → ExitCode

exit : {a : Set} → ExitCode → IO a
exit success = exit′ success
exit (failure (ec , _)) = exit′ (failure ec)

postulate
  die : {a : Set} → String → IO a

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
