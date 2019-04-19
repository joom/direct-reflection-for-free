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
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Dependent where

import Data.Typeable
import Data.Data

import qualified Data.Map as M
import Data.Maybe

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Debug.Trace

data Var =
    Str String
  | Gensym String Int
  | Dummy
  deriving (Show, Eq, Ord, Data, Typeable)

data Definition =
    Axiom Var Ty
  | Defn  Var Ty Exp
  | Data  Var Ty [(Var, Ty)]
  deriving (Show, Data, Typeable)

data Abs = Abs Var Ty Exp deriving (Show, Eq, Data, Typeable)

data Exp =
    Var Var
  | Universe Int
  | Pi Abs
  | Lam Abs
  | App Exp Exp
  deriving (Show, Eq, Data, Typeable)

type Ty = Exp

data Env = Env { sym :: Int }

type Ctx = M.Map Var (Exp, Maybe Exp)

type TcM m = ExceptT [String] (StateT Env (ReaderT Ctx m))

fresh :: Monad m => Var -> TcM m Var
fresh Dummy = pure Dummy
fresh (Gensym x _) = fresh (Str x)
fresh (Str x) = do
  ctr <- gets sym
  modify (\e -> e { sym = ctr + 1})
  pure (Gensym x ctr)

fresh' :: Monad m => String -> TcM m Var
fresh' = fresh . Str

subst' :: Monad m => M.Map Var Exp -> Abs -> TcM m Abs
subst' ctx (Abs x ty env) = do
  x' <- fresh x
  ty' <- subst ctx ty
  env' <- subst (M.insert x (Var x') ctx) env
  pure $ Abs x' ty' env'

subst :: Monad m => M.Map Var Exp -> Exp -> TcM m Exp
subst ctx =
  \case
    Pi abs -> Pi <$> subst' ctx abs
    Lam abs -> Lam <$> subst' ctx abs
    App f v -> App <$> subst ctx f <*> subst ctx v
    v@(Var x) -> pure $ M.findWithDefault v x ctx
    u@(Universe _) -> pure u

substInto :: Monad m => Var -> Exp -> Exp -> TcM m Exp
substInto v e = subst (M.singleton v e)

lookupType
  :: Monad m
  => Var -> TcM m Exp
lookupType x = do
  res <- asks (fmap fst . M.lookup x)
  case res of
    Just ty -> pure ty
    Nothing -> throwError ["The context contains no binding named " ++ prettyVar x]

lookupValue
  :: Monad m
  => Var -> TcM m (Maybe Exp)
lookupValue x = do
  res <- asks (fmap snd . M.lookup x)
  case res of
    Just val -> pure val
    Nothing -> throwError [prettyVar x ++ " has not been bound to any value."]

extendCtx :: Var -> Exp -> Maybe Exp -> Ctx -> Ctx
extendCtx x ty val = M.insert x (ty, val)

extendCtx' :: Var -> Exp -> Ctx -> Ctx
extendCtx' x ty = M.insert x (ty, Nothing)

inferType :: Monad m => Exp -> TcM m Exp
inferType =
  \case
    Var x -> lookupType x
    Universe u -> pure $ Universe (u + 1)
    Pi (Abs x ty exp) -> do
      ty' <- inferUniverse ty
      exp' <- local (extendCtx' x ty) (inferUniverse exp)
      pure (Universe (max ty' exp'))
    Lam (Abs x ty exp) -> do
      ty' <- inferUniverse ty
      exp' <- local (extendCtx' x ty) (inferType exp)
      pure (Pi (Abs x ty exp'))
    App f v -> do
      (Abs x s ty) <- inferPi f
      ty' <- inferType v
      checkEq s ty'
      substInto x v ty

inferUniverse :: Monad m => Exp -> TcM m Int
inferUniverse exp = do
  ty <- inferType exp
  norm <- normalize ty
  case norm of
    Universe k -> pure k
    _          -> throwError [pretty exp ++ " is not a universe"]

inferPi :: Monad m => Exp -> TcM m Abs
inferPi exp = do
  ty <- inferType exp
  norm <- normalize ty
  case norm of
    Pi k -> pure k
    _    -> throwError [pretty exp ++ " is not a pi-abstraction"]

normalize :: Monad m => Exp -> TcM m Exp
normalize =
  \case
    v@(Var x) -> do
      val <- lookupValue x
      case val of
        Nothing  -> pure v
        Just exp -> normalize exp
    App f v -> do
      nv <- normalize v
      nf <- normalize f
      case nf of
        Lam (Abs x ty f') -> do
          nf' <- substInto x v f'
          normalize nf'
        f' -> pure $ App f' nv
    u@(Universe _) -> pure u
    Pi a -> Pi <$> normalizeAbs a
    Lam a -> Lam <$> normalizeAbs a

normalizeAbs :: Monad m => Abs -> TcM m Abs
normalizeAbs (Abs x ty exp) = do
  ty' <- normalize ty
  exp' <- local (extendCtx x ty' Nothing) $ normalize exp
  pure (Abs x ty' exp')

checkEq :: Monad m => Exp -> Exp -> TcM m ()
checkEq s ty = do
  isEq <- equalInCtx s ty
  unless isEq $ throwError [pretty s ++ " ≠ " ++ pretty ty ++ " in the current context"]

equalInCtx :: Monad m => Exp -> Exp -> TcM m Bool
equalInCtx a b = do
  a' <- normalize a
  b' <- normalize b
  equalInCtx' a' b'

  where
    equalInCtx' (Var v) (Var v')           = pure $ v == v'
    equalInCtx' (Universe k) (Universe k') = pure $ k == k'
    equalInCtx' (App f v) (App f' v')      = pure $ (f == f') && (v == v')
    equalInCtx' (Pi p) (Pi p')             = equalAbs p p'
    equalInCtx' (Lam p) (Lam p')           = equalAbs p p'
    equalInCtx' _ _                        = pure False

    equalAbs (Abs x ty exp) (Abs x' ty' exp') = do
      exp'' <- substInto x' (Var x) exp'
      pure $ (ty == ty') && (exp' == exp'')

initialEnv :: Env
initialEnv = Env {sym = 0}

initialCtx :: Ctx
initialCtx = M.fromList []

typecheck :: MonadIO m => TcM m a -> m ()
typecheck prog = do
  result <- flip runReaderT initialCtx . flip evalStateT initialEnv . runExceptT $ prog
  liftIO $ case result of
    Left err -> mapM_ (putStrLn . ("Error: " ++)) err
    Right _  -> putStrLn "Finished without errors."

ppType :: MonadIO m => Var -> TcM m ()
ppType x = do
  let px = prettyVar x
  ty <- lookupType x
  liftIO . putStrLn $ px ++ " : " ++ pretty ty

ppExp :: MonadIO m => Exp -> TcM m ()
ppExp x = do
  let px = pretty x
  liftIO . putStrLn $ px

  x' <- normalize x
  when (x /= x') $
    liftIO . putStrLn $ "  = " ++ pretty x'

  ty <- inferType x
  liftIO . putStr $ "  : " ++ pretty ty

  norm <- normalize ty
  liftIO .
    putStrLn $
      (if ty == norm
         then ""
         else "  ~ " ++ pretty norm) ++ "\n"


prettyVar :: Var -> String
prettyVar (Str s)      = s
prettyVar (Gensym s i) = s ++ show i
prettyVar Dummy        = "dummy"

pair (Abs v t e) = "(" ++ prettyVar v ++ " : " ++ pretty t ++ ")"
pair' (v, t) = "(" ++ prettyVar v ++ " : " ++ pretty t ++ ")"

pretty :: Exp -> String
pretty (Var v) = prettyVar v
pretty (Universe k) = "Type " ++ show k
pretty lam@(Lam _) =
  let (as, e) = collectAbstractions lam
  in "λ " ++ unwords (map pair' as) ++ ". " ++ wrapIfNeeded e
pretty pi@(Pi _) =
  let (as, e) = collectAbstractions pi
  in "Π " ++ unwords (map pair' as) ++ ". " ++ wrapIfNeeded e
pretty (App e e') = wrapIfNeeded e ++ " " ++ wrapIfNeeded e'

wrapIfNeeded :: Exp -> String
wrapIfNeeded (Var v) = prettyVar v
wrapIfNeeded e       = "(" ++ pretty e ++ ")"

collectAbstractions :: Exp -> ([(Var, Ty)], Exp)
collectAbstractions (Lam (Abs v t lam@(Lam _))) = ((v,t) : x, y)
  where (x,y) = collectAbstractions lam
collectAbstractions (Lam (Abs v t e)) = ([(v,t)], e)
collectAbstractions (Pi (Abs v t pi@(Pi _))) = ((v,t) : x, y)
  where (x,y) = collectAbstractions pi
collectAbstractions (Pi (Abs v t e)) = ([(v,t)], e)
collectAbstractions e = ([], e)

main :: IO ()
main = typecheck $ do
  ppExp (Pi (Abs (Str "a") (Universe 0)
            (Pi (Abs (Str "x") (Var (Str "a"))
                (Var (Str "a"))))))
