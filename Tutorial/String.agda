
module Tutorial.String where

open import Tutorial.Bool
open import Tutorial.List
open import Tutorial.Nat
open import Data.Function

postulate
  String : Set
  Char   : Set
{-# BUILTIN STRING String #-}
{-# BUILTIN CHAR Char #-}

{-# COMPILE GHC String = type String #-}
{-# COMPILE GHC Char = type Char #-}

primitive
  primStringAppend   : String -> String -> String
  primStringToList   : String -> List Char
  primStringFromList : List Char -> String
  primStringEquality : String -> String -> Bool

stringToList = primStringToList
listToString = primStringFromList

eqString = primStringEquality

infixr 40 _+++_
_+++_ = primStringAppend

strCat : List String -> String
strCat ss = foldr _+++_ "" ss

strLen : String -> Nat
strLen = length ∘ primStringToList
