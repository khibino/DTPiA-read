
module Tutorial.List where

open import Tutorial.Bool
open import Tutorial.Nat

infixr 30 _::_ _++_

data List (A : Set) : Set where
  []   : List A
  _::_ : (x : A)(xs : List A) -> List A

{-# BUILTIN LIST List #-}

{-# COMPILE GHC List = data [] = ([] | (:)) #-}

_++_ : {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f z [] = z
foldr f z (x :: xs) = f x (foldr f z xs)

concat : {A : Set} -> List (List A) -> List A
concat = foldr _++_ []

[_] : {A : Set} -> A -> List A
[ x ] = x :: []

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (x :: xs) with p x
... | true  = x :: filter p xs
... | false = filter p xs

length : {A : Set} -> List A -> Nat
length []        = zero
length (_ :: xs) = suc (length xs)
