
--  import qualified GHC.Types as GHC

{-# FOREIGN GHC
  import qualified Data.Text.IO as TIO
  #-}

open import Tutorial.Unit
open import Tutorial.String

postulate IO : Set -> Set
{-# COMPILE GHC IO = type IO #-}
{-# BUILTIN IO IO #-}


postulate
  putStrLn : String -> IO Unit

{-# COMPILE GHC putStrLn = TIO.putStrLn #-}

main : IO Unit
main = putStrLn "Hello world!"

-----

postulate
  return : {A : Set} -> A -> IO A
  _>>=_  : {A B : Set} -> IO A -> (A -> IO B) -> IO B

{-# COMPILE GHC return = (\a -> return)  #-}
{-# COMPILE GHC _>>=_  = (\a b -> (>>=))  #-}
