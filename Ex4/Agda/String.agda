
module Ex4.Agda.String where

open import Tutorial.List using (List)

{-# FOREIGN GHC
  import qualified Data.Text as T
  #-}

postulate
  Char : Set
  Text : Set

{-# BUILTIN CHAR Char #-}
{-# BUILTIN STRING Text #-}

String : Set
String = List Char

postulate
  unpackT : Text -> String

{-# COMPILE GHC unpackT = T.unpack #-}
