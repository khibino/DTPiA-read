
open import Tutorial.Unit using (Unit; unit)
open import Tutorial.List using ([]; _::_; _++_)
open import Data.Function using (_∘_)
open import Data.Pair using (_×_; fst)
open import Data.Either using (Either)

open import Views using (Cxt; Type; Raw; Infer; ok; bad; infer)

open import Ex4.Agda.String using (String; unpackT)
open import Ex4.Agda.IO using (IO; getContents; putStrLn; fail; _>>=_; return)

{-# FOREIGN GHC
  import Ex4.Parser (Parser, runParser)
  import Ex4.LambdaSyntax (ty, topExpr)
  #-}

postulate
  Parser : Set -> Set
{-# COMPILE GHC Parser = type Parser #-}

postulate
  either : {A B C : Set} -> (A -> C) -> (B -> C) -> Either A B -> C
  runParser : {A : Set} -> Parser A -> String -> Either String (A × String)
  topExpr : Parser Raw
  showExpr : Raw -> String
  showType : Type -> String
{-# COMPILE GHC either = \_ _ _ -> either #-}
{-# COMPILE GHC runParser = \_ -> runParser #-}
{-# COMPILE GHC topExpr = topExpr #-}
{-# COMPILE GHC showExpr = show #-}
{-# COMPILE GHC showType = show #-}

runRaw : IO Unit
runRaw =
  getContents >>=
  either
    (fail ∘ (unpackT "Raw-expression Parse error: " ++_))
    (putStrLn ∘ showExpr ∘ fst)
  ∘ runParser topExpr

putInferred : {Γ : Cxt}{e : Raw} -> Infer Γ e -> IO Unit
putInferred {_} {_} (ok τ t) = putStrLn (showType τ)
putInferred {_} {e}  bad      = fail (unpackT "Fail to inference type for expression: " ++ showExpr e)

runInfer : IO Unit
runInfer =
  getContents >>=
  either
    (fail ∘ (unpackT "Raw-expression Parse error: " ++_))
    (putInferred ∘ infer [] ∘ fst)
  ∘ runParser topExpr

main : IO Unit
main = runInfer
-- main = runRaw
