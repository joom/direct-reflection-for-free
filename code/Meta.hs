{-|
The goal is to get a mechanism like elaborator reflection for free,
using Haskell's generics.

In a few languages implemented in Haskell, there's a mechanism for reflecting
the terms in the object language (whatever language is being implemented) to
terms in the meta language (in this case, Haskell), and for reify terms in the meta language to the object language.
Idris does this to simplify the implementation of its metaprogramming facilities. Dhall does this for evaluation of Dhall terms.



-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Meta where

import GHC.Generics

class Reflect exp a where
  reflect :: a -> exp
  default reflect :: (Generic a, GReflect exp (Rep a)) => a -> exp
  reflect x = greflect (from x)

class GReflect exp f where
  greflect :: f a -> exp

class Monad m => Reify m exp a where
  reify :: exp -> m a
  default reify :: (Generic a, GReify m exp (Rep a)) => exp -> m a
  reify x = greify (to x)

class Monad m => GReify m exp f where
  greify :: exp -> m (f a)

data Exp = Var String | App Exp Exp | Lam String Ty Exp
data Ty = Unit | String | Arr Ty Ty

-- instance GReify m Exp V1 where
--   greify x = _


