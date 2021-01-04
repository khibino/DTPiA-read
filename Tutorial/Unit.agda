
module Tutorial.Unit where

data Unit : Set where
  unit : Unit

{-# COMPILE GHC Unit = data () () #-}
