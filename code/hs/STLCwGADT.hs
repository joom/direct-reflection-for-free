{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

module GADT2 where

import Data.Type.Equality
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH

data Nat :: * where
  Z :: Nat
  S :: Nat -> Nat

deriving instance Show Nat
deriving instance Eq Nat
deriving instance Ord Nat

data Ty :: * where
  TyUnit   :: Ty
  TyString :: Ty
  Arr      :: Ty -> Ty -> Ty
  Sum      :: Ty -> Ty -> Ty
  Pair     :: Ty -> Ty -> Ty
  TyVar    :: String -> Ty
  Mu       :: String -> Ty -> Ty

deriving instance Show Ty
deriving instance Eq Ty

data Exp :: Ty -> * where
  MkUnit :: Exp TyUnit
  StrLit :: String -> Exp TyString
  Var    :: forall t. String -> Exp t
  Abs    :: forall t1 t2. String -> Exp t2 -> Exp (Arr t1 t2)
  App    :: forall t1 t2. Exp (Arr t1 t2) -> Exp t1 -> Exp t2
  Inl    :: forall t1 t2. Exp t1 -> Exp (Sum t1 t2)
  Inr    :: forall t1 t2. Exp t2 -> Exp (Sum t1 t2)
  MkPair :: forall t1 t2. Exp t1 -> Exp t2 -> Exp (Pair t1 t2)

deriving instance Show (Exp a)
-- deriving instance Eq (Exp a)

-- type family   TypeOf (a :: *)     = (t :: Ty) | t -> a
type family   TypeOf (a :: *)     = (t :: Ty)
type instance TypeOf String       = TyString
-- type instance TypeOf ()           = TyUnit
-- type instance TypeOf (a -> b)     = Arr  (TypeOf a) (TypeOf b)
-- type instance TypeOf (Either a b) = Sum  (TypeOf a) (TypeOf b)
-- type instance TypeOf (a, b)       = Pair (TypeOf a) (TypeOf b)
-- type instance TypeOf (Exp a) =
--     Mu "Exp" (Sum TyUnit
--               (Sum TyString
--                 (Sum TyString
--                   (Pair TyString (TyVar "Exp")))))

class Bridge a where
  reify   :: a              -> Exp (TypeOf a)
  reflect :: Exp (TypeOf a) -> Maybe a

instance Bridge String where
  reify s = StrLit s
  reflect (StrLit s) = Just s
  reflect _ = Nothing

genBridge :: TH.Name -> TH.DecsQ
genBridge typeName = do
    TH.TyConI (TH.DataD _ _ _ _ ctors _) <- TH.reify typeName
    let argsOfCtors = map (map (TH.AppT (TH.ConT ''TypeOf)))
                    $ map args ctors :: [[TH.Type]]


    return [typeInst, inst]
  where
    args :: TH.Con -> [TH.Type]
    args (TH.GadtC _ xs _) = map snd xs
    args (TH.ForallC _ _ c) = args c
    args _ = [] -- TODO


    pat = foldl1 TH.AppT [TH.ConT typeName]
    res = TH.PromotedT 'TyUnit
    typeInst = TH.TySynInstD ''TypeOf (TH.TySynEqn [pat] res)


    defns = [ TH.FunD 'reify   []
            , TH.FunD 'reflect []
            ]
    inst = TH.InstanceD Nothing [] (TH.AppT (TH.ConT ''Bridge) (TH.ConT typeName)) defns
