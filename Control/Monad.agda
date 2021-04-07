
module Control.Monad
  {M : Set -> Set}
  (ret : {A : Set} -> A -> M A)
  (bind : {A B : Set} -> M A -> (A -> M B) -> M B)
  where

return = ret

_>>=_ = bind
