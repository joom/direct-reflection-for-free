{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

module GADT2 where

import qualified Data.Map as M

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH

data Nat :: * where
  S :: Nat -> Nat
  Z :: Nat

deriving instance Show Nat
deriving instance Eq Nat
deriving instance Ord Nat

pred :: Nat -> Nat
pred Z = Z
pred (S n) = n

type family Pred (n :: Nat) :: Nat where
  Pred Z = Z
  Pred (S n) = n

-- | Finite natural numbers.
-- The maximum value of type 'Fin (S n)' would correspond to 'n'.
data Fin (n :: Nat) :: * where
  FS :: Fin n -> Fin (S n)
  FZ :: Fin (S n)

deriving instance Show (Fin n)
deriving instance Eq (Fin n)
deriving instance Ord (Fin n)

-- TODO coerce
weakenFin :: Fin n -> Fin (S n)
weakenFin FZ = FZ
weakenFin (FS n) = FS (weakenFin n)

data Vect (n :: Nat) (a :: *) :: * where
  Vnil :: Vect Z a
  Vcons :: a -> Vect n a -> Vect (S n) a

deriving instance Show a => Show (Vect n a)
deriving instance Eq a => Eq (Vect n a)

-- | Takes an index and a vector and selects the elements at the index,
-- as long as the index is within the length of the vector.
nth :: Fin n -> Vect n a -> a
nth FZ     (Vcons x _)  = x
nth (FS n) (Vcons _ xs) = nth n xs

instance Functor (Vect n) where
  fmap _ Vnil = Vnil
  fmap f (Vcons x xs) = Vcons (f x) (fmap f xs)

-- | Type of lambda calculus expressions,
-- indexed by the number of different free variables that may occur in the expression.
-- Uses the de Bruijn style nameless representation of variables.
data Exp (n :: Nat) :: * where
  StrLit :: String -> Exp n
  Var    :: Fin n -> Exp n
  Abs    :: Exp (S n) -> Exp n
  App    :: Exp n -> Exp n -> Exp n

-- TODO coerce
weakenExp :: Exp n -> Exp (S n)
weakenExp (StrLit s) = StrLit s
weakenExp (Var n) = Var (weakenFin n)
weakenExp (Abs e) = Abs (weakenExp e)
weakenExp (App e1 e2) = App (weakenExp e1) (weakenExp e2)

deriving instance Show (Exp n)
deriving instance Eq (Exp n)

s :: Exp Z
s = Abs (Abs (Abs (App (App (Var (FS (FS FZ))) (Var FZ)) (App (Var (FS FZ)) (Var FZ)))))

k :: Exp Z
k = Abs (Abs (Var (FS FZ)))

i :: Exp Z
i = Abs (Var FZ)

type Ctx n = Vect n (Exp n)


-- subst :: Exp n -> Fin n -> Exp (Pred n) -> Exp (Pred n)
-- subst (Var v') v t = undefined
-- subst (App e1 e2) v t = App (subst e1 v t) (subst e2 v t)
-- subst (Abs body) v t = Abs (subst body (FS v) undefined)
-- subst (StrLit s) _ _ = StrLit s

eval' :: Ctx n -> Exp n -> Exp n
eval' ctx (Var x) = nth x ctx
eval' ctx (App (Abs body) e) = undefined -- eval' (fmap weakenExp (Vcons e ctx)) body
eval' ctx (App e1 e2)
  | eval' ctx e1 == e1 && eval' ctx e2 == e2 = App e1 e2
  | otherwise = eval' ctx (App (eval' ctx e1) (eval' ctx e2))
eval' _ e = e

eval :: Exp Z -> Exp Z
eval = eval' Vnil

class Bridge a where
  reify   :: forall n. a     -> Exp n
  reflect :: forall n. Exp n -> Maybe a

instance Bridge String where
  reify s = StrLit s
  reflect (StrLit s) = Just s
  reflect _ = Nothing

-- instance Bridge (Exp n) where
--   reify s = undefined
--   reflect _ = Nothing

-- | Get the name of the type variable binder,
-- regardless of whether it is a plain or kinded variable.
getBndrVar :: TH.TyVarBndr -> TH.Name
getBndrVar (TH.PlainTV n) = n
getBndrVar (TH.KindedTV n _) = n

-- | Generate a 'Bridge' instance for the given type name.
genBridge :: TH.Name -> TH.DecsQ
genBridge typeName = do
    -- Get information about the type we are inspecting,
    -- specifically the indices and constructors of the type.
    TH.TyConI (TH.DataD _ _ bndrs _ ctors _) <- TH.reify typeName
    -- Create fully qualified type. If 'typeName' is 'Exp', give me 'Exp n'.
    let qual = foldl TH.AppT (TH.ConT typeName) (map (TH.ConT . getBndrVar) bndrs)

    return [TH.InstanceD Nothing [] (TH.AppT (TH.ConT ''Bridge) qual) defns]
  where
    defns = [ TH.FunD 'reify   []
            , TH.FunD 'reflect []
            ]
