{-# LANGUAGE DeriveDataTypeable #-}
module Test where

import Data.Data
import Data.Typeable

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

data Tree = Leaf | Node Int Forest
  deriving (Show, Eq, Ord, Data, Typeable)
data Forest = Nil | Cons Tree Forest
  deriving (Show, Eq, Ord, Data, Typeable)

single :: Tree
single = Node 1 Nil

balanced :: Tree
balanced = Node 2 (Cons (Node 1 Nil) (Cons (Node 3 Nil) Nil))

data A = UnitA | MkA B deriving (Show, Eq, Ord, Data, Typeable)
data B = UnitB | MkB C deriving (Show, Eq, Ord, Data, Typeable)
data C = UnitC | MkC A deriving (Show, Eq, Ord, Data, Typeable)

data Inf a = MkInf (Inf a) deriving (Show, Eq, Ord, Data, Typeable)
