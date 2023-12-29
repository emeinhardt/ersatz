{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_HADDOCK not-home #-}
--------------------------------------------------------------------
-- |
-- Copyright :  © Edward Kmett 2010-2014, Johan Kiviniemi 2013
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
--------------------------------------------------------------------

module Ersatz.Equatable.Poly
  ( Equatable(..)
  , GEquatable(..)
  ) where

import Prelude hiding ((&&),(||),not,and,or,all,any)

import Ersatz.Bit
import GHC.Generics
import Numeric.Natural
import Control.Arrow ((***))
import Data.Composition ((.:))
import Data.IntMap (IntMap)
import Data.Foldable (toList)
import Data.Map (Map)
import Data.Int
import Data.Word
import Data.Void
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Sequence as Seq
import qualified Data.Tree as Tree

infix  4 ===, /==

-- | Instances for this class for arbitrary types can be automatically derived from 'Generic'.
class Boolean b => Equatable t b where
  -- | Compare for equality within the SAT problem.
  (===) :: t -> t -> b
  default (===) :: (Generic t, GEquatable (Rep t) b) => t -> t -> b
  a === b = from a ===# from b

  -- | Compare for inequality within the SAT problem.
  (/==) :: t -> t -> b

  a /== b = not (a === b)

instance Equatable Bool Bit where
  (===) = not . uncurry xor . (bool *** bool) .: (,)
  (/==) = uncurry xor . (bool *** bool) .: (,)

instance Equatable Bool Bool where
  a === b = not (xor a b)
  (/==) = xor

instance Equatable Bit Bit where
  a === b = not (xor a b)
  (/==) = xor

instance (Eq k, Equatable v b) => Equatable (Map k v) b where
  x === y
    | Map.keys x == Map.keys y = Map.elems x === Map.elems y
    | otherwise                = false

instance Equatable v b => Equatable (IntMap v) b where
  x === y
    | IntMap.keys x == IntMap.keys y = IntMap.elems x === IntMap.elems y
    | otherwise                      = false

instance Equatable v b => Equatable (Seq.Seq v) b where
  x === y
    | Seq.length x == Seq.length y = toList x === toList y
    | otherwise                    = false

-- manually written because ancient GHC didn't have the generics instance
instance Equatable a b => Equatable (Tree.Tree a) b where
  Tree.Node x xs === Tree.Node y ys = x === y && xs === ys

instance (Equatable a τ, Equatable b τ) => Equatable (a,b) τ
instance (Equatable a τ, Equatable b τ, Equatable c τ) => Equatable (a,b,c) τ
instance (Equatable a τ, Equatable b τ, Equatable c τ, Equatable d τ) => Equatable (a,b,c,d) τ
instance (Equatable a τ, Equatable b τ, Equatable c τ, Equatable d τ, Equatable e τ) => Equatable (a,b,c,d,e)  τ
instance (Equatable a τ, Equatable b τ, Equatable c τ, Equatable d τ, Equatable e τ, Equatable f τ) => Equatable (a,b,c,d,e,f) τ
instance (Equatable a τ, Equatable b τ, Equatable c τ, Equatable d τ, Equatable e τ, Equatable f τ, Equatable g τ) => Equatable (a,b,c,d,e,f,g) τ
instance Equatable a b => Equatable (Maybe a) b
instance Equatable a b => Equatable [a] b
instance Equatable a b => Equatable (NonEmpty a) b
instance (Equatable a τ, Equatable b τ) => Equatable (Either a b) τ

class (Boolean b) => GEquatable f b where
  (===#) :: f a -> f a -> b

instance Boolean b => GEquatable U1 b where
  U1 ===# U1 = true

instance Boolean b => GEquatable V1 b where
  x ===# y = x `seq` y `seq` error "GEquatable[V1].===#"

instance (GEquatable f b, GEquatable g b) => GEquatable (f :*: g) b where
  (a :*: b) ===# (c :*: d) = (a ===# c) && (b ===# d)

instance (GEquatable f b, GEquatable g b) => GEquatable (f :+: g) b where
  L1 a ===# L1 b = a ===# b
  R1 a ===# R1 b = a ===# b
  _ ===# _ = false

instance GEquatable f b => GEquatable (M1 i c f) b where
  M1 x ===# M1 y = x ===# y

instance Equatable a b => GEquatable (K1 i a) b where
  K1 a ===# K1 b = a === b

-- Boring instances that end up being useful when deriving Equatable with Generics

instance Boolean b => Equatable ()       b  where _ === _ = true
instance Boolean b => Equatable Void     b  where x === y = x `seq` y `seq` error "Equatable[Void].==="
instance Boolean b => Equatable Int      b  where x === y = bool (x == y)
instance Boolean b => Equatable Integer  b  where x === y = bool (x == y)
instance Boolean b => Equatable Natural  b  where x === y = bool (x == y)
instance Boolean b => Equatable Word     b  where x === y = bool (x == y)
instance Boolean b => Equatable Word8    b  where x === y = bool (x == y)
instance Boolean b => Equatable Word16   b  where x === y = bool (x == y)
instance Boolean b => Equatable Word32   b  where x === y = bool (x == y)
instance Boolean b => Equatable Word64   b  where x === y = bool (x == y)
instance Boolean b => Equatable Int8     b  where x === y = bool (x == y)
instance Boolean b => Equatable Int16    b  where x === y = bool (x == y)
instance Boolean b => Equatable Int32    b  where x === y = bool (x == y)
instance Boolean b => Equatable Int64    b  where x === y = bool (x == y)
instance Boolean b => Equatable Char     b  where x === y = bool (x == y)
instance Boolean b => Equatable Float    b  where x === y = bool (x == y)
instance Boolean b => Equatable Double   b  where x === y = bool (x == y)
instance Boolean b => Equatable Ordering b  where x === y = bool (x == y)
instance Boolean b => Equatable Bool     b  where x === y = bool (x == y)
