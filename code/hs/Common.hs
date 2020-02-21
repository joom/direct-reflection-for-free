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
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Common where

import Data.Array
import Data.Graph
import Data.List
import Data.Typeable
import Data.Data
import Unsafe.Coerce

import Debug.Trace

-- Generic programming
castWith :: forall a b. a :~: b -> a -> b
castWith Refl = unsafeCoerce

cong :: forall f a b. a :~: b -> f a :~: f b
cong Refl = Refl

sym :: forall a b. a :~: b -> b :~: a
sym Refl = Refl

getTypeRep :: forall a. Typeable a => TypeRep
getTypeRep = typeOf @a undefined

getDataType :: forall a. Data a => DataType
getDataType = dataTypeOf @a undefined

getConstrs :: forall a. Data a => [Constr]
getConstrs = getDataTypeConstrs (getDataType @a)

data D = forall a. Data a => D a

mkD :: forall a. Data a => D
mkD = D (undefined :: a)

dRep :: D -> TypeRep
dRep (D x) = typeOf x

instance Show D where
  show x = show (dRep x)

-- | Since 'D' is only a way to represent type objects as values in a
-- reversible way, it suffices to compare the types.
instance Eq D where
  x == y = dRep x == dRep y

instance Ord D where
  x `compare` y = dRep x `compare` dRep y

dConstrs :: D -> [Constr]
dConstrs (D a) = case dataTypeRep (dataTypeOf a) of
                   AlgRep constrs -> constrs
                   _ -> []

getDataTypeConstrs :: DataType -> [Constr]
getDataTypeConstrs (dataTypeRep -> AlgRep cs) = cs
getDataTypeConstrs _ = []

getNumOfConstrs :: forall a. Data a => Int
getNumOfConstrs = length (getConstrs @a)

constrArgs :: D -> Constr -> [D]
constrArgs (D a) c = gmapQ D (mkConstr a c)
  where mkConstr :: forall a. Data a => a -> Constr -> a
        mkConstr _ = fromConstr

allConstrArgs :: D -> [[D]]
allConstrArgs d = constrArgs d <$> dConstrs d

recD :: D -> [[D]]
recD entry = filter (elem entry) (nub (map (map v') (cycles g)))
  where
    args :: D -> [D]
    args = concat . allConstrArgs

    depEdges :: [D] -> [D] -> [(D, [D])]
    depEdges _ [] = []
    depEdges seen (d : ds)
      | d `elem` seen = depEdges seen ds
      | otherwise = (d, args d) : depEdges (d : seen) (args d ++ ds)

    (g, v) = graphFromEdges' (map (\(x,y) -> (x,x,y)) (depEdges [] [entry]))

    v' :: Vertex -> D
    v' = (\(x,_,_) -> x) . v

-- | A function that finds all cycles in a graph.  A cycle is given as a
-- finite list of the vertices in order of occurrence, where each vertex
-- only appears once. Written by Chris Smith, April 20, 2009.
-- <https://cdsmith.wordpress.com/2009/04/20/code-for-manipulating-graphs-in-haskell/>
cycles :: Graph -> [[Vertex]]
cycles g = concatMap cycles' (vertices g)
  where cycles' v   = build [] v v
        build p s v =
          let p'         = p ++ [v]
              local      = [ p' | x <- (g!v), x == s ]
              good w     = w > s && not (w `elem` p')
              ws         = filter good (g ! v)
              extensions = concatMap (build p' s) ws
          in  local ++ extensions
