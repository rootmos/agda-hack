module Overture.IORef where

open import Overture.IO using (IO)
open import Data.Unit using (⊤)

postulate
  IORef : (a : Set) → Set
  newIORef : ∀ {a} → a → IO (IORef a)
  readIORef : ∀ {a} → IORef a → IO a
  writeIORef : ∀ {a} → IORef a → a → IO ⊤

{-# FOREIGN GHC import qualified Data.IORef as R #-}
{-# COMPILE GHC IORef = type R.IORef #-}
{-# COMPILE GHC newIORef = \ _ -> R.newIORef #-}
{-# COMPILE GHC readIORef = \ _ -> R.readIORef #-}
{-# COMPILE GHC writeIORef = \ _ -> R.writeIORef #-}
