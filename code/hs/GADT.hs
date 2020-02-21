{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module GADT where

import Data.Type.Equality
import Data.Function

data Type :: * -> * where
  TInt    :: Type Int
  TBool   :: Type Bool
  TArrow  :: Type a -> Type b -> Type (a -> b)

class TypeOf a where
  typeOf :: a -> Type a

instance TypeOf Int where
  typeOf _ = TInt

instance TypeOf Bool where
  typeOf _ = TBool

data Bop :: * -> * -> * where
  Add  :: Bop Int Int
  Sub  :: Bop Int Int
  Eq   :: Bop Int Bool
  Lt   :: Bop Int Bool
  Gt   :: Bop Int Bool
  And  :: Bop Bool Bool
  Or   :: Bop Bool Bool

data Expr :: * -> * where
  Lit     :: TypeOf a => a -> Expr a
  Var     :: String -> Type a -> Expr a
  Lambda  :: String -> Type a -> Expr b -> Expr (a -> b)
  App     :: Expr (a -> b) -> Expr a -> Expr b
  Bop     :: Bop a b -> Expr a -> Expr a -> Expr b
  If      :: Expr Bool -> Expr a -> Expr a -> Expr a
  Lift    :: a -> Type a -> Expr a

plus :: Expr (Int -> Int -> Int)
plus = Lambda "x" TInt $ Lambda "y" TInt $ Bop Add (Var "x" TInt) (Var "y" TInt)

abs :: Expr (Int -> Int)
abs = Lambda "x" TInt $ If (Bop Lt (Var "x" TInt) (Lit 0))
               {- then -}  (Bop Sub (Lit 0) (Var "x" TInt))
               {- else -}  (Var "x" TInt)

class TypeOfExpr a where
  typeOfExpr :: Expr a -> Type a

instance TypeOfExpr Int where
  typeOfExpr _ = TInt

instance TypeOfExpr Bool where
  typeOfExpr _ = TBool

instance TypeOfExpr b => TypeOfExpr (a -> b) where
  typeOfExpr (Var _ t)      = t
  typeOfExpr (Lambda _ t e) = TArrow t $ typeOfExpr e
  typeOfExpr (App e1 _)     = case typeOfExpr e1 of
                                TArrow _ t2 -> t2
  typeOfExpr (If _ e1 _)    = typeOfExpr e1
  typeOfExpr (Lift _ t)     = t

eqTy :: Type u -> Type v -> Maybe (u :~: v)
eqTy TInt  TInt  = Just Refl
eqTy TBool TBool = Just Refl
eqTy (TArrow u1 u2) (TArrow v1 v2) = do
  Refl <- eqTy u1 v1
  Refl <- eqTy u2 v2
  return Refl
eqTy _     _     = Nothing

subst :: String -> u -> Type u -> Expr t -> Expr t
subst _ _ _ (Lit b) = Lit b
subst x v u (Var y t)
    | x == y    = case eqTy u t of
                    Just Refl -> Lift v u
                    Nothing   -> error "ill-typed substitution"
    | otherwise = Var y t
subst x v u (Bop b e1 e2) = Bop b
                            (subst x v u e1)
                            (subst x v u e2)
subst x v u (If e1 e2 e3) = If (subst x v u e1)
                               (subst x v u e2)
                               (subst x v u e3)
subst x v u (Lambda y t e) | x == y    = Lambda y t e
                           | otherwise = Lambda y t (subst x v u e)
subst x v u (App e1 e2) = App (subst x v u e1) (subst x v u e2)
subst _ _ _ (Lift x t)  = Lift x t

evalBop :: Bop a b -> a -> a -> b
evalBop Add = (+)
evalBop Sub = (-)
evalBop Eq  = (==)
evalBop Lt  = (<)
evalBop Gt  = (>)
evalBop And = (&&)
evalBop Or  = (||)

eval :: Expr t -> t
eval (Lit v)        = v
eval (Var _ _)      = error "Free variable has no value"
eval (Lambda x t e) = \v -> eval $ subst x v t e
eval (App e1 e2)    = (eval e1) (eval e2)
eval (Bop b e1 e2)  = (evalBop b `on` eval) e1 e2
eval (If b e1 e2)   | eval b    = eval e1
                    | otherwise = eval e2
eval (Lift x _)     = x
