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
import System.Console.Haskeline

import Common

import Data.Typeable
import Data.Data

data Op = Plus | Minus | Times | Div | Concat
  deriving (Show, Eq, Ord, Data, Typeable)

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
  | Prim Op
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
    parseOp = (string "+" *> return Plus)
          <|> (string "-" *> return Minus)
          <|> (string "*" *> return Times)
          <|> (string "/" *> return Div)
          <|> (string "^" *> return Concat)
    nonApp = try parseUnit <|> parens exp
            <|> parseString <|> parseInt
            <|> quote exp <|> antiquote exp <|> evalBr exp <|> parseBr exp <|> prettyBr exp
            <|> parseAbs <|> parseVar <|> (Prim <$> parseOp)
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
pretty (Prim op) = case op of
                     Plus -> "+"
                     Minus -> "-"
                     Times -> "*"
                     Div -> "/"
                     Concat -> "^"

lams :: [String] -> Exp -> Exp
lams xs e = foldr Abs e xs

apps :: [Exp] -> Exp
apps = foldl1 App

type Ctx = M.Map String Exp

-- TODO fix variable capture and evaluation under lambda
-- evaluation under lambda should be reconsidered for compile-time evaluation of quotes
eval' :: M.Map String Exp -> Exp -> Exp
eval' env e@(Var x) = fromMaybe e (M.lookup x env)
eval' env (App (App eop@(Prim op) e1) e2) =
  case (eval' env e1, eval' env e2) of
    (IntLit i1, IntLit i2) | Just f <- lookup op [ (Plus, (+))
                                                 , (Minus, (-))
                                                 , (Times, (*))
                                                 , (Div, div) ] -> IntLit (f i1 i2)
    (StrLit s1, StrLit s2) | op == Concat -> StrLit (s1 ++ s2)
    (e1', e2') -> (App (App eop e1') e2')
eval' env (App (Abs x body) e) = eval' (M.insert x (eval' env e) env) body
eval' env (App e1 e2)
  | eval' env e1 == e1 && eval' env e2 == e2 = App e1 e2
  | otherwise = eval' env (App (eval' env e1) (eval' env e2))
eval' env e@(Abs x body) = e
-- eval' env (Abs x body) = Abs x $ eval' (M.insert x (Var x) env) body
eval' env (Quasiquote e) = reify e
eval' env (Antiquote e) = fromJust (reflect (eval e))
eval' env (Parse e) = let StrLit s = eval e in
                      case parseExp s of
                        Left err -> error $ show err
                        Right e' -> reify e'
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
  reify :: a -> Exp
  reflect :: Exp -> Maybe a

instance Bridge String where
  reify s = StrLit s
  reflect (StrLit s) = Just s
  reflect _ = Nothing

instance Bridge Int where
  reify n = IntLit n
  reflect (IntLit n) = Just n
  reflect _ = Nothing

-- instance (Bridge a, Bridge b) => Bridge (a -> b) where
--   reify f = Abs "x" (App undefined (Var "x"))
--   reflect (Abs x e) = undefined
--   reflect _ = Nothing

instance Data a => Bridge a where
  reify v
    | Just eq <- eqT @a @Int    = reify (castWith eq v)
    | Just eq <- eqT @a @String = reify (castWith eq v)
    | otherwise =
        lams args (apps (Var c : gmapQ reifyArg v))
    where
      (args, c) = constrToScott @a (toConstr v)
      reifyArg :: forall d. Data d => d -> Exp
      reifyArg x = reify @d x

  reflect e
    | Just eq <- eqT @a @Int    = castWith (cong (sym eq)) (reflect e)
    | Just eq <- eqT @a @String = castWith (cong (sym eq)) (reflect e)
    | otherwise =
      case collectAbs e of -- dissect the nested lambdas
        ([], _) -> Nothing
        (args, body) ->
          case spineView body of -- dissect the nested application
            (Var c, rest) -> do
                let ctors = getConstrs @a
                ctor <- lookup c (zip args ctors)
                evalStateT (fromConstrM reflectArg ctor) rest
            _ -> Nothing
    where
      reflectArg :: forall d. Data d => StateT [Exp] Maybe d
      reflectArg = do e <- gets head
                      modify tail
                      lift (reflect @d e)

roundTrip :: forall a. Data a => a -> Maybe a
roundTrip x = reflect @a ((reify @a x))

reifyIO :: forall a. Data a => a -> IO ()
reifyIO x = putStrLn $ pretty $ reify @a x

repl :: IO ()
repl = runInputT defaultSettings loop
  where
    loop = do
      x <- getInputLine ">> "
      case parseExp <$> x of
        Nothing -> loop
        Just (Left err) -> liftIO (putStr "ERROR" >> print err) >> loop
        Just (Right exp) -> (liftIO . putStrLn . pretty . eval $ exp) >> loop

main :: IO ()
main = repl

{-

Example programs:

~((\x. x) `( () ))

We quote the unit expression, get a reified representation of the unit term,
apply that to the identity function, get the same thing back,
and then splice it back.

~((\x y. x) `(1) `(0))

We quote both 1 and 0. We also have a Scott encoding of the boolean term true.
This term is its own eliminator. In other words, it's an if expression.
If the boolean is true, we get the quoted 1, if it's false we get the quoted 0.
Then we splice it back, which gives us the numeral 1. The boolean was true after all.

These are all generative examples. Let's do one that is intentional. (inspecting terms)

(\t. t (\x. 1) (\e1 e2. 2) (\x e. 2) (\s. 1) (\i. 1) 0 (\e. 1) (\e. 1) (\e. 1) (\e. 1) (\e. 1) (\op. 1)) `(f x)

This program consists of two parts, a function and the quoted term 'f x'.
The function takes a reified AST, and returns however many arguments
are needed at the top level for that AST node.

(\f. (\z. f (z z)) (\z. f (z z)))
  (\size t. t (\x. 1) (\e1 e2. + (size e1) (size e2)) (\x e. size e) (\s. 1) (\i. 1) 0 (\e. size e) (\e. size e) (\e. size e) (\e. size e) (\e. size e) (\op. 1)) `(f x)

(\f. (\z. f (z z)) (\z. f (z z))) (\size t. t (\x. 1) (\e1 e2. + 1 (+ (size e1) (size e2))) (\x e. + 1 (size e)) (\s. 1) (\i. 1) 0 (\e. + 1 (size e)) (\e. + 1 (size e)) (\e. + 1 (size e)) (\e. + 1 (size e)) (\e. + 1 (size e)) (\op. 1)) `(f x)



-}

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
