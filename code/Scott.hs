{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Scott where

import qualified Data.Map as M
import Data.Maybe
import Control.Monad.State.Strict
import Text.Parsec.String
import Text.Parsec

import Common

import Data.Typeable
import Data.Data

-- Lambda calculus
data Exp =
    Var String       -- x
  | App Exp Exp      -- e1 e2
  | Abs String Exp   -- \x.x or λx.x, also works with nested \x y.x and such
  | StrLit String    -- "asdf", can escape "as\"df"
  | IntLit Int       -- 0
  | MkUnit           -- ()
  | Quasiquote Exp   -- `(e), where e is any expression
  | Antiquote Exp    -- ~(e), where e is an AST in Scott encoding
  | Eval Exp         -- [|e|], where e is an AST in Scott encoding, returns AST
  | Parse Exp        -- {e}, where e is a string expression, returns AST
  | Pretty Exp       -- [e], where e is an AST in Scott encoding, returns a string
  deriving (Show, Eq, Ord, Data, Typeable)

parseExp :: String -> Either ParseError Exp
parseExp input = parse exp "λ−calculus" input
  where
    lexeme p = spaces *> p <* spaces
    parens p = char '(' *> p <* char ')'
    quote p = string "`(" *> (Quasiquote <$> p) <* char ')'
    antiquote p = string "~(" *> (Antiquote <$> p) <* char ')'
    evalBr p = string "[|" *> (Eval <$> p) <* string "|]"
    parseBr p = char '{' *> (Parse <$> p) <* char '}'
    prettyBr p = char '[' *> (Pretty <$> p) <* char ']'
    name = (:) <$> letter <*> many (digit <|> letter)
    parseAbs = do
      (char '\\' <|> char 'λ')
      vs <- many1 (lexeme name)
      lexeme $ char '.'
      body <- exp
      return $ foldr Abs body vs
    parseVar = Var <$> name
    parseUnit = string "()" *> return MkUnit
    escape = do
        d <- char '\\'
        c <- oneOf "\\\"0nrvtbf" -- all the characters which can be escaped
        return [d, c]
    nonEscape = noneOf "\\\"\0\n\r\v\t\b\f"
    character = fmap return nonEscape <|> escape
    parseString = char '"' *> (StrLit . concat <$> many character) <* char '"'
    parseInt = IntLit . read <$> many1 (digit :: Parser Char)
    nonApp = try parseUnit <|> parens exp
            <|> parseString <|> parseInt
            <|> quote exp <|> antiquote exp <|> evalBr exp <|> parseBr exp <|> prettyBr exp
            <|> parseAbs <|> parseVar
    exp = chainl1 (lexeme nonApp) $ return App

pretty :: Exp -> String
pretty (Var s) = s
pretty e@(App _ _) = "(" ++ go e ++ ")"
  where go (App e1 e2) = go e1 ++ " " ++ pretty e2
        go e = pretty e
pretty e@(Abs _ _) = "(λ" ++ go e ++ ")"
  where go (Abs x e) = " " ++ x ++ go e
        go e = ". " ++ pretty e
pretty (StrLit s) = "\"" ++ s ++ "\""
pretty (IntLit i) = show i
pretty MkUnit = "()"
pretty (Quasiquote e) = "`(" ++ pretty e ++ ")"
pretty (Antiquote e) = "~(" ++ pretty e ++ ")"

lams :: [String] -> Exp -> Exp
lams xs e = foldr Abs e xs

apps :: [Exp] -> Exp
apps = foldl1 App

type Ctx = M.Map String Exp

eval' :: M.Map String Exp -> Exp -> Exp
eval' env e@(Var x) = fromMaybe e (M.lookup x env)
eval' env (App (Abs x body) e) = eval' (M.insert x (eval' env e) env) body
eval' env (App e1 e2)
  | eval' env e1 == e1 && eval' env e2 == e2 = App e1 e2
  | otherwise = eval' env (App (eval' env e1) (eval' env e2))
eval' env (Abs x body) = Abs x $ eval' (M.insert x (Var x) env) body
eval' env (Quasiquote e) = reflect e
eval' env (Antiquote e) = fromJust (reify (eval e))
eval' env (Parse e) = let StrLit s = eval e in
                      case parseExp s of
                        Left err -> error $ show err
                        Right e' -> reflect e'
eval' env (Pretty e) = StrLit $ pretty e
eval' env e = e

eval :: Exp -> Exp
eval = eval' M.empty

collectAbs :: Exp -> ([String], Exp)
collectAbs (Abs x e) = let (l, e') = collectAbs e in (x:l, e')
collectAbs e = ([], e)

spineView :: Exp -> (Exp, [Exp])
spineView (App e1 e2) = let (f, l) = spineView e1 in (f, l ++ [e2])
spineView e = (e, [])

constrToScott :: forall a. Data a => Constr -> ([String], String)
constrToScott c = (ctorArgs, ctorArgs !! (constrIndex c - 1))
  where
    names s = map ((s ++) . show) [0..]
    ctorArgs = take (getNumOfConstrs @a) (names "c")

    -- ^ arg names representing each ctor
-- The interesting type class
class Bridge a where
  reflect :: a -> Exp
  reify :: Exp -> Maybe a

instance Bridge String where
  reflect s = StrLit s
  reify (StrLit s) = Just s
  reify _ = Nothing

instance Bridge Int where
  reflect n = IntLit n
  reify (IntLit n) = Just n
  reify _ = Nothing

-- instance (Bridge a, Bridge b) => Bridge (a -> b) where
--   reflect f = Abs "x" (App undefined (Var "x"))
--   reify (Abs x e) = undefined
--   reify _ = Nothing

instance Data a => Bridge a where
  reflect v
    | Just eq <- eqT @a @Int    = reflect (castWith eq v)
    | Just eq <- eqT @a @String = reflect (castWith eq v)
    | otherwise =
        lams args (apps (Var c : gmapQ reflectArg v))
    where
      (args, c) = constrToScott @a (toConstr v)
      reflectArg :: forall d. Data d => d -> Exp
      reflectArg x = reflect @d x

  reify e
    | Just eq <- eqT @a @Int    = castWith (cong (sym eq)) (reify e)
    | Just eq <- eqT @a @String = castWith (cong (sym eq)) (reify e)
    | otherwise =
      case collectAbs e of -- dissect the nested lambdas
        ([], _) -> Nothing
        (args, body) ->
          case spineView body of -- dissect the nested application
            (Var c, rest) -> do
                let ctors = getConstrs @a
                ctor <- lookup c (zip args ctors)
                evalStateT (fromConstrM reifyArg ctor) rest
            _ -> Nothing
    where
      reifyArg :: forall d. Data d => StateT [Exp] Maybe d
      reifyArg = do e <- gets head
                    modify tail
                    lift (reify @d e)

roundTrip :: forall a. Data a => a -> Maybe a
roundTrip x = reify @a ((reflect @a x))

reflectIO :: forall a. Data a => a -> IO ()
reflectIO x = putStrLn $ pretty $ reflect @a x

-- | Very rudimentary REPL, ideally we'd like to use repline or haskeline
-- but I wanted to make the module self-contained.
repl :: IO ()
repl = do
  putStr ">> "
  x <- getLine
  case parseExp x of
    Left err -> putStr "ERROR: " >> print err
    Right exp -> putStrLn (pretty $ eval exp)
  repl

main :: IO ()
main = repl

-- Takes a Scott encoding of lambda terms and changes it into their Mogensen encoding
-- toMogensen :: Exp -> Exp
-- toMogensen e
--     | fromJust (lookup c argMap) == toConstr (Var undefined) =
--         let [StrLit s] = rest
--         in lams args (apps [Var c, Var s])
--     | fromJust (lookup c argMap) == toConstr (Abs undefined undefined) =
--         let [StrLit s, lamBody] = rest
--         in lams args (apps [Var c, Abs s (toMogensen lamBody)])
--     | otherwise =
--   where
--     (args, body) = collectAbs e
--     (Var c, rest) = spineView body
--     argMap = zip args (fromJust (getConstrs @Exp))
