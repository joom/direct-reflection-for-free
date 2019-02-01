{-|
The goal is to get a mechanism like elaborator reflection for free,
using Haskell's generics.

In a few languages implemented in Haskell, there's a mechanism for reflecting
the terms in the object language (whatever language is being implemented) to
terms in the meta language (in this case, Haskell), and for reify terms in the meta language to the object language.
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
module Scott where

import qualified Data.Map as M
import Data.Maybe
import Control.Monad.State.Strict

import Debug.Trace
import Unsafe.Coerce

import Data.Typeable
import Data.Data

-- Absbda calculus

data Exp =
    Var String
  | App Exp Exp
  | Abs String Exp
  | StrLit String
  | IntLit Int
  | MkUnit
  | Quasiquote Exp
  | Antiquote Exp
  deriving (Show, Eq, Ord, Data, Typeable)

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

isFree :: String -> Exp -> Bool
isFree x (Var s) = x /= s
isFree x (App e1 e2) = isFree x e1 && isFree x e2
isFree x (Abs y e) = x == y || isFree x e
isFree _ _ = True

eval' :: M.Map String Exp -> Exp -> Exp
eval' env e@(Var x) = fromMaybe e (M.lookup x env)
eval' env (App (Abs x body) e) = eval' (M.insert x (eval' env e) env) body
eval' env (App e1 e2)
  | eval' env e1 == e1 && eval' env e2 == e2 = App e1 e2
  | otherwise = eval' env (App (eval' env e1) (eval' env e2))
eval' env (Abs x body) = Abs x $ eval' (M.insert x (Var x) env) body
eval' env (Quasiquote e) = reflect e
eval' env (Antiquote e) = fromJust (reify (eval e))
eval' env e = e

eval = eval' M.empty


-- Generic programming

getTypeRep :: forall a. Typeable a => TypeRep
getTypeRep = typeOf @a undefined

getDataType :: forall a. Data a => DataType
getDataType = dataTypeOf @a undefined

getConstrs :: forall a. Data a => Maybe [Constr]
getConstrs = case dataTypeRep (getDataType @a) of
               AlgRep cs -> Just cs
               _ -> Nothing

getNumOfConstrs :: forall a. Data a => Int
getNumOfConstrs = maybe 0 id (length <$> getConstrs @a)

constrToScott :: forall a. Data a => Constr -> ([String], String)
constrToScott c = (ctorArgs, ctorArgs !! (constrIndex c - 1))
  where
    names s = map ((s ++) . show) [0..]
    ctorArgs = take (getNumOfConstrs @a) (names "c") -- arg names representing each ctor

collectAbs :: Exp -> ([String], Exp)
collectAbs (Abs x e) = let (l, e') = collectAbs e in (x:l, e')
collectAbs e = ([], e)

spineView :: Exp -> (Exp, [Exp])
spineView (App e1 e2) = let (f, l) = spineView e1 in (f, l ++ [e2])
spineView e = (e, [])

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

instance Data a => Bridge a where
  reflect v
    | getTypeRep @a == getTypeRep @Int = reflect @Int (unsafeCoerce v)
    | getTypeRep @a == getTypeRep @String = reflect @String (unsafeCoerce v)
    | otherwise =
      -- trace ("\nDATA for " ++ show (getTypeRep @a) ++ "\n") $
        lams args (apps (Var c : gmapQ reflectArg v))
    where
      (args, c) = constrToScott @a (toConstr v)
      reflectArg :: forall d. Data d => d -> Exp
      reflectArg x = reflect @d x

  reify e
    | getTypeRep @a == getTypeRep @Int = unsafeCoerce (reify @Int e)
    | getTypeRep @a == getTypeRep @String = unsafeCoerce <$> (reify @String e)
    | otherwise =
      case collectAbs e of -- dissect the nested lambdas
        ([], _) -> Nothing
        (args, body) ->
          case spineView body of -- dissect the nested application
            (Var c, rest) -> do
                ctors <- getConstrs @a
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


-- num :: Int -> Exp
-- num n = Abs "s" $ Abs "z" $ foldr App (Var "z") (replicate n ((Var "s")))

data Nat = S Nat | Z deriving (Show, Eq, Ord, Data, Typeable)
three = S (S (S Z))

data Number = Num Int deriving (Show, Eq, Ord, Data, Typeable)

data Color =
    Red
  | Green
  | Blue
  deriving (Show, Eq, Ord, Data, Typeable)

data Tree a =
    Empty
  | Node a (Tree a) (Tree a)
  deriving (Show, Eq, Ord, Data, Typeable)

balanced :: Tree Int
balanced = Node 2 (Node 1 Empty Empty) (Node 3 Empty Empty)
