
module Ex4.Agda.IO where

open import Tutorial.Unit using (Unit)

open import Ex4.Agda.String using (String)

postulate IO : Set -> Set
{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

postulate
  getContents : IO String
  putStrLn : String -> IO Unit
  fail : {A : Set} -> String -> IO A

{-# COMPILE GHC getContents = getContents #-}
{-# COMPILE GHC putStrLn = putStrLn #-}
{-# COMPILE GHC fail = (\a -> fail) #-}

postulate
  return : {A : Set} -> A -> IO A
  _>>=_  : {A B : Set} -> IO A -> (A -> IO B) -> IO B

{-# COMPILE GHC return = (\a -> return)  #-}
{-# COMPILE GHC _>>=_  = (\a b -> (>>=))  #-}
