
module Tutorial.Integer where

open import Tutorial.Nat

-- Haskell integers
-- postulate Integer : Set
data Integer : Set where
  pos    : Nat -> Integer
  negsuc : Nat -> Integer

{-# BUILTIN INTEGER Integer #-}
{-# BUILTIN INTEGERPOS pos #-}
{-# BUILTIN INTEGERNEGSUC negsuc #-}
{-# COMPILE GHC Integer = type Integer #-}

-- primitive
--   primIntegerAbs   : Integer -> Nat
--   primNatToInteger : Nat -> Integer

-- intToNat = primIntegerAbs
natToInt = pos
