module Ex4.Parser (
  Parser (..), runParser,
  LastError, errorM, throwE, perrorM,
  token, eof, satisfy, char, string,
  ) where

import Control.Applicative (Alternative (empty, (<|>)))
import Control.Monad (liftM, ap, MonadPlus (mplus), guard)

---

type LastError = Maybe String

errorM :: String -> LastError
errorM = Just

---

newtype Parser a =
  Parser { unParser :: String -> Either LastError (a, String) }

throwE :: LastError -> Parser a
throwE e = Parser $ \_  -> Left e

token :: Parser Char
token = Parser $ \s -> case s of
  []   -> Left $ errorM "token: end of input"
  c:cs -> return (c, cs)

eof :: Parser ()
eof = Parser $ \s -> case s of
  []  -> return ((), [])
  c:_ -> Left $ errorM $ "eof: more token: " ++ show c

pureP :: a -> Parser a
pureP a = Parser $ \in_ -> return (a, in_)

bindP :: Parser a -> (a -> Parser b) -> Parser b
pa `bindP` pf = Parser $ \in0 -> do
  (a, in1) <- unParser pa in0
  unParser (pf a) in1

---

instance Functor Parser where
  fmap = liftM

instance Applicative Parser where
  pure = pureP
  (<*>) = ap

instance Monad Parser where
  return = pureP
  (>>=) = bindP

instance Alternative Parser where
  empty = Parser $ \_ -> Left Nothing
  p1 <|> p2 = Parser $
              \s -> case unParser p1 s of
                      Left e1 -> case unParser p2 s of
                        Left Nothing       -> Left e1
                        e2@(Left (Just _)) -> e2
                        y@(Right _)        -> y
                      x@(Right _)          -> x

instance MonadPlus Parser where
  mplus = (<|>)

---

perrorM :: String -> Parser a
perrorM = throwE . errorM

satisfy :: (Char -> Bool) -> Parser Char
satisfy p = do
  c <- token
  guard (p c) <|> perrorM ("safisty: not satisfied token: " ++ show c)
  return c

---

runParser :: Parser a -> String -> Either String (a, String)
runParser p in_ =
  either
  (Left . maybe "<empty error>" id)
  Right
  $ unParser p in_

char :: Char -> Parser Char
char c = satisfy (== c)

string :: String -> Parser String
string = mapM char
