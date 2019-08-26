{-|
The goal is to get a mechanism like elaborator reifyion for free,
using Haskell's generics.

In a few languages implemented in Haskell, there's a mechanism for reifying
the terms in the object language (whatever language is being implemented) to
terms in the meta language (in this case, Haskell), and for reflect terms in the meta language to the object language.
Idris does this to simplify the implementation of its metaprogramming facilities. Dhall does this for evaluation of Dhall terms.
-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module STLC where

import Data.List
import qualified Data.Map as M
import Data.Maybe
import Control.Monad.State.Strict

import Text.Parsec
import Text.Parsec.String
import qualified Text.Parsec.Expr as P

import Debug.Trace
import Common
import Test

import Data.Typeable
import Data.Data

data Ty =
    TyUnit
  | TyVoid
  | TyString
  | TyInt
  | Arr Ty Ty
  | Pair Ty Ty
  | Sum Ty Ty
  | Mu String Ty
  | TyVar String
  deriving (Show, Eq, Ord, Data, Typeable)

type Arg = (String, Ty)

data Exp =
    Var String
  | App Exp Exp
  | Abs Arg Exp
  | Fold Exp
  | Unfold Exp
  | StrLit String
  | IntLit Int
  | Inl Exp Ty
  | Inr Exp Ty
  | MkPair Exp Exp
  | MkUnit
  | Let Stmt Exp
  -- | Quasiquote Exp
  -- | Antiquote Exp
  -- | Parse Exp
  -- | Pretty Exp
  deriving (Show, Eq, Ord, Data, Typeable)

data Stmt =
    Defn String Exp
  deriving (Show, Eq, Ord, Data, Typeable)

lexeme p = spaces *> p <* spaces
parens p = char '(' *> p <* char ')'
name = (:) <$> letter <*> many (digit <|> letter)

tyParser :: Parser Ty
tyParser = muLevel
  where
    muLevel = parseMu <|> nonMu
    parseMu = do
      (string "mu" <|> string "μ")
      vs <- many1 (lexeme name)
      lexeme $ char '.'
      body <- nonMu
      return $ foldr Mu body vs
    parseVar = TyVar <$> name
    nonMu  = P.buildExpressionParser table atom
    atom = parens muLevel
        <|> (lexeme (string "unit") *> return TyUnit)
        <|> (lexeme (string "void") *> return TyVoid)
        <|> (lexeme (string "string") *> return TyString)
        <|> (lexeme (string "int") *> return TyInt)
        <|> (TyVar <$> name)
    table = [ [bin "*" Pair] , [bin "+" Sum] , [bin "->" Arr] ]
    bin name fun = P.Infix (lexeme (string name) *> return fun) P.AssocLeft

parseExp :: String -> Either ParseError Exp
parseExp input = parse exp "λ−calculus" input
  where
    parseArg = parens $ (,) <$> lexeme name <*> (lexeme (char ':') *> tyParser)
    parseAbs = do
      (string "\\" <|> string "λ" <|> string "lam")
      vs <- many1 parseArg
      lexeme $ char '.'
      body <- exp
      return $ foldr Abs body vs
    parseVar = Var <$> name
    unit = lexeme (string "()") *> return MkUnit
    nonApp = unit <|> parens exp <|> parseAbs <|> parseVar
    exp = chainl1 (lexeme nonApp) $ return App

prettyTy :: Ty -> String
prettyTy TyUnit = "unit"
prettyTy TyVoid = "void"
prettyTy TyString = "string"
prettyTy TyInt = "int"
prettyTy (TyVar x) = x
prettyTy e@(Mu _ _) = "(μ" ++ go e ++ ")"
  where go (Mu x e) = " " ++ x ++ go e
        go e = ". " ++ prettyTy e
prettyTy (Sum t1 t2) = "(" ++ prettyTy t1 ++ "+" ++ prettyTy t2 ++ ")"
prettyTy (Pair t1 t2) = "(" ++ prettyTy t1 ++ "*" ++ prettyTy t2 ++ ")"
prettyTy e@(Arr _ _) = "(" ++ go e ++ ")"
  where go (Arr e1 e2) = go e1 ++ " -> " ++ prettyTy e2
        go e = prettyTy e

pretty :: Exp -> String
pretty (Var s) = s
pretty e@(App _ _) = "(" ++ go e ++ ")"
  where go (App e1 e2) = go e1 ++ " " ++ pretty e2
        go e = pretty e
pretty e@(Abs _ _) = "(λ" ++ go e ++ ")"
  where go (Abs (x, ty) e) = " (" ++ show x ++ " : " ++ prettyTy ty ++ ")" ++ go e
        go e = ". " ++ pretty e
pretty (StrLit s) = "\"" ++ s ++ "\""
pretty (IntLit i) = show i
pretty (Inl e t) = "(inl " ++ pretty e ++ " as " ++ prettyTy t ++ ")"
pretty (Inr e t) = "(inr " ++ pretty e ++ " as " ++ prettyTy t ++ ")"
pretty (MkPair e1 e2) = "(" ++ pretty e1 ++ " , " ++ pretty e2 ++ ")"
pretty MkUnit = "()"
-- pretty (Quasiquote e) = "`(" ++ pretty e ++ ")"
-- pretty (Antiquote e) = "~(" ++ pretty e ++ ")"

lams :: [Arg] -> Exp -> Exp
lams xs e = foldr Abs e xs

apps :: [Exp] -> Exp
apps = foldl1 App

isFree :: String -> Exp -> Bool
isFree x (Var s) = x /= s
isFree x (App e1 e2) = isFree x e1 && isFree x e2
isFree x (Abs (y, _) e) = x == y || isFree x e
isFree _ _ = True

eval' :: M.Map String Exp -> Exp -> Exp
eval' env e@(Var x) = fromMaybe e (M.lookup x env)
eval' env (App (Abs (x, _) body) e) = eval' (M.insert x (eval' env e) env) body
eval' env (App e1 e2)
  | eval' env e1 == e1 && eval' env e2 == e2 = App e1 e2
  | otherwise = eval' env (App (eval' env e1) (eval' env e2))
eval' env (Abs (x, ty) body) = Abs (x, ty) $ eval' (M.insert x (Var x) env) body
-- eval' env (Quasiquote e) = reify e
-- eval' env (Antiquote e) = fromJust (reflect (eval e))
-- eval' env (Parse e) = let StrLit s = eval e in
--                       case parseExp s of
--                         Left err -> error $ show err
--                         Right e' -> e'
-- eval' env (Pretty e) = StrLit $ pretty e
eval' env (Unfold (Fold e)) = eval e
eval' env (Unfold e) =
  case eval e of
    Fold e' -> e
    _ -> Unfold (eval e)
eval' env (Fold e) = Fold (eval e)
eval' env e = e

eval = eval' M.empty

substTy :: String -> Ty -> Ty -> Ty
substTy x v(Arr t1 t2) = Arr (substTy x v t1) (substTy x v t2)
substTy x v(Sum t1 t2) = Sum (substTy x v t1) (substTy x v t2)
substTy x v(Pair t1 t2) = Pair (substTy x v t1) (substTy x v t2)
substTy x v (Mu y t) | x /= y = Mu y (substTy x v t) -- capture!!!
substTy x v (TyVar y) | x == y = v
substTy _ _ t = t

inferTy' :: M.Map String Ty -> Exp -> Maybe Ty
inferTy' _ MkUnit = return TyUnit
inferTy' _ (IntLit _) = return TyInt
inferTy' _ (StrLit _) = return TyString
inferTy' ctx (App e1 e2) = do
  t1 <- inferTy' ctx e1
  case t1 of
    Arr dom ran -> do
      t2 <- inferTy' ctx e2
      if dom == t2
        then return ran
        else Nothing
    _ -> Nothing
inferTy' ctx (Var x) = M.lookup x ctx
inferTy' ctx (Abs (x, ty) body) = Arr ty <$> inferTy' (M.insert x ty ctx) body
inferTy' ctx (Fold e) = undefined
inferTy' ctx (Unfold e) = do
  t <- inferTy' ctx e
  case t of
    Mu x body -> return (substTy x (Mu x body) body)
    _ -> Nothing
inferTy' ctx (MkPair e1 e2) = Pair <$> inferTy' ctx e1 <*> inferTy' ctx e2
inferTy' ctx (Inl e t) = do
  t1' <- inferTy' ctx e
  case t of
    Sum t1 t2 | t1 == t1' -> Just t
    _ -> Nothing
inferTy' ctx (Inr e t) = do
  t2' <- inferTy' ctx e
  case t of
    Sum t1 t2 | t1 == t2' -> Just t
    _ -> Nothing

inferTy :: Exp -> Maybe Ty
inferTy = inferTy' M.empty

collectAbs :: Exp -> ([Arg], Exp)
collectAbs (Abs x e) = let (l, e') = collectAbs e in (x:l, e')
collectAbs e = ([], e)

spineView :: Exp -> (Exp, [Exp])
spineView (App e1 e2) = let (f, l) = spineView e1 in (f, l ++ [e2])
spineView e = (e, [])

-- The interesting type class
class Bridge a where
  ty :: Ty
  reify :: a -> Exp
  reflect :: Exp -> Maybe a

instance Bridge String where
  ty = TyString
  reify s = StrLit s
  reflect (StrLit s) = Just s
  reflect _ = Nothing

instance Bridge Int where
  ty = TyInt
  reify n = IntLit n
  reflect (IntLit n) = Just n
  reflect _ = Nothing

dTy :: D -> Ty
dTy (D (x :: a)) = ty @a

foldr1def :: Foldable t => (a -> a -> a) -> a -> t a -> a
foldr1def f base t | null t = base
                   | otherwise = foldr1 f t

instance Data a => Bridge a where
  ty
    | Just eq <- eqT @a @Int    = TyInt
    | Just eq <- eqT @a @String = TyString
    | otherwise = foldr Mu (foldr1def Sum TyVoid argsTy) (map show rec)
        where
          d = mkD @a
          rec = nub (concat (recD d))
          dTy' a = if a `elem` rec then TyVar (show a) else dTy a
          argsTy = map (foldr1def Pair TyUnit . map dTy') (allConstrArgs d)

  reify v
    | Just eq <- eqT @a @Int    = reify (castWith eq v)
    | Just eq <- eqT @a @String = reify (castWith eq v)
    | otherwise = folds $
      case getConstrs @a of
        [] -> error $ "You can't have a value of the type " ++ show (mkD @a) ++ " since it has no constructors"
        _ -> sums (getConstrs @a) (foldr1def MkPair MkUnit (gmapQ reifyArg v))
      where
        rec = nub (concat (recD (mkD @a)))
        folds e = iterate Fold e !! length rec
        -- argMap = zip (getConstrs @a) (allConstrArgs (mkD @a))

        sums :: [Constr] -> Exp -> Exp
        sums [x, y] e | x == toConstr v = Inl e undefined
                      | y == toConstr v = Inr e undefined
        sums [x] e = e
        sums (x:xs) e | x == toConstr v = Inl e undefined
                      | otherwise = Inr (sums xs e) undefined

        reifyArg :: forall d. Data d => d -> Exp
        reifyArg x = reify @d x

  reflect e
    | Just eq <- eqT @a @Int    = castWith (cong (sym eq)) (reflect e)
    | Just eq <- eqT @a @String = castWith (cong (sym eq)) (reflect e)
    | otherwise =
        if length rec /= numFolds then Nothing else
        if iSum >= length ctors then Nothing else
        evalStateT (fromConstrM reflectArg ctor) rest
      where
        rec = nub (concat (recD (mkD @a)))

        countFolds n (Fold e) = countFolds (n + 1) e
        countFolds n e = (n, e)

        (numFolds, e') = countFolds 0 e
        ctors = getConstrs @a

        countSums n e | n + 1 == length ctors = (n, e)
        countSums n (Inr (Inr e t) t') = countSums (n + 1) (Inr e t)
        countSums n (Inr (Inl e t) t') = (n + 1, e)
        countSums n (Inr e t) = (n + 1, e)
        countSums n (Inl e t) = (n, e)
        countSums n e = (n, e)

        -- we should only strip Inl/Inr as much as it's allowed
        (iSum, e'') = countSums 0 e'
        ctor = ctors !! iSum
        args = allConstrArgs (mkD @a) !! iSum

        -- we should only strip MkPair as much as it's allowed
        collectFromPair n e | n + 1 == length args = [e]
        collectFromPair n (MkPair x y) = x : collectFromPair (n + 1) y
        collectFromPair n e = [e]

        rest = collectFromPair 0 e''

        reflectArg :: forall d. Data d => StateT [Exp] Maybe d
        reflectArg = do e <- gets head
                        modify tail
                        lift (reflect @d e)

roundTrip :: forall a. Data a => a -> Maybe a
roundTrip x = reflect @a ((reify @a x))

reifyIO :: forall a. Data a => a -> IO ()
reifyIO x = putStrLn $ pretty $ reify @a x
