{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
#ifndef HLINT
{-# LANGUAGE DefaultSignatures #-}
#endif
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
module Ersatz.Orderable
  ( Orderable(..)
  , GOrderable(..)
  ) where

import Prelude hiding ((&&),(||),not,and,or,all,any)

import Data.Foldable (toList)
import Data.Int
import Data.Void
import Data.Word
import Ersatz.Bit
import Ersatz.Equatable
import GHC.Generics
import Numeric.Natural
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Tree as Tree

infix  4 <?, <=?, >=?, >?

-- | Instances for this class for arbitrary types can be automatically derived from 'Generic'.
class Equatable t b => Orderable t b where
  -- | Compare for less-than within the SAT problem.
  (<?)  :: t -> t -> b

  -- | Compare for less-than or equal-to within the SAT problem.
  (<=?) :: t -> t -> b
  x <=? y = x === y || x <? y
#ifndef HLINT
  default (<?) :: (Generic t, GOrderable (Rep t) b) => t -> t -> b
  a <? b = from a <?# from b
#endif

  -- | Compare for greater-than or equal-to within the SAT problem.
  (>=?) :: t -> t -> b
  x >=? y = y <=? x

  -- | Compare for greater-than within the SAT problem.
  (>?) :: t -> t -> b
  x >? y = y <? x


instance Orderable Bit Bit where
  a <?  b = not a && b
  a <=? b = not a || b

-- | Compare by lexicographic order on sorted key-value pairs
instance (Ord k, Orderable v b) => Orderable (Map.Map k v) b where
  x <?  y = assocsLt (Map.assocs x) (Map.assocs y)
  x <=? y = assocsLe (Map.assocs x) (Map.assocs y)

-- | Compare by lexicographic order on sorted key-value pairs
instance Orderable v b => Orderable (IntMap.IntMap v) b where
  x <?  y = assocsLt (IntMap.assocs x) (IntMap.assocs y)
  x <=? y = assocsLe (IntMap.assocs x) (IntMap.assocs y)

assocsLt :: (Ord k, Orderable v b) => [(k,v)] -> [(k,v)] -> b
assocsLt _ [] = false
assocsLt [] _ = true
assocsLt ((k1,v1):xs) ((k2,v2):ys) =
  case compare k1 k2 of
    LT -> true
    GT -> false
    EQ -> v1 <? v2 || v1 === v2 && assocsLt xs ys

assocsLe :: (Ord k, Orderable v b) => [(k,v)] -> [(k,v)] -> b
assocsLe [] _ = true
assocsLe _ [] = false
assocsLe ((k1,v1):xs) ((k2,v2):ys) =
  case compare k1 k2 of
    LT -> true
    GT -> false
    EQ -> v1 <? v2 || v1 === v2 && assocsLe xs ys

-- | Compare by lexicographic order on elements
instance Orderable v b => Orderable (Seq.Seq v) b where
  x <?  y = toList x <?  toList y
  x <=? y = toList x <=? toList y

-- | Compare by lexicographic order on: root node, list of children
instance Orderable a b => Orderable (Tree.Tree a) b where
  Tree.Node x xs <?  Tree.Node y ys = (x,xs) <?  (y,ys)
  Tree.Node x xs <=? Tree.Node y ys = (x,xs) <=? (y,ys)

instance (Orderable a τ, Orderable b τ) => Orderable (a,b) τ
instance (Orderable a τ, Orderable b τ, Orderable c τ) => Orderable (a,b,c) τ
instance (Orderable a τ, Orderable b τ, Orderable c τ, Orderable d τ) => Orderable (a,b,c,d) τ
instance (Orderable a τ, Orderable b τ, Orderable c τ, Orderable d τ, Orderable e τ) => Orderable (a,b,c,d,e) τ
instance (Orderable a τ, Orderable b τ, Orderable c τ, Orderable d τ, Orderable e τ, Orderable f τ) => Orderable (a,b,c,d,e,f) τ
instance (Orderable a τ, Orderable b τ, Orderable c τ, Orderable d τ, Orderable e τ, Orderable f τ, Orderable g τ) => Orderable (a,b,c,d,e,f,g) τ
instance Orderable a τ => Orderable (Maybe a) τ
instance (Orderable a τ, Orderable b τ) => Orderable (Either a b) τ

-- | Lexicographic order
instance Orderable a b => Orderable [a] b where
#ifndef HLINT
  []   <? []   = false
  x:xs <? y:ys = x === y && xs <? ys
              || x <?  y
  []   <? _    = true
  _    <? []   = false

  []   <=? _    = true
  x:xs <=? y:ys = x === y && xs <=? ys
               || x <?  y
  _    <=? []   = false
#endif

class GEquatable f b => GOrderable f b where
  (<?#) :: f a -> f a -> b
  (<=?#) :: f a -> f a -> b

instance Boolean b => GOrderable U1 b where
  U1 <?#  U1 = false
  U1 <=?# U1 = true

instance Boolean b => GOrderable V1 b where
  x <?# y = x `seq` y `seq` error "GOrderable[V1].<?#"
  x <=?# y = x `seq` y `seq` error "GOrderable[V1].<=?#"

instance (GOrderable f b, GOrderable g b) => GOrderable (f :*: g) b where
  (a :*: b) <?#  (c :*: d) = (a <?# c) || (a ===# c && b <?# d)
  (a :*: b) <=?# (c :*: d) = (a <?# c) || (a ===# c && b <=?# d)

instance (GOrderable f b, GOrderable g b) => GOrderable (f :+: g) b where
  L1 _ <?# R1 _ = true
  L1 a <?# L1 b = a <?# b
  R1 a <?# R1 b = a <?# b
  R1 _ <?# L1 _ = false

  L1 _ <=?# R1 _ = true
  L1 a <=?# L1 b = a <=?# b
  R1 a <=?# R1 b = a <=?# b
  R1 _ <=?# L1 _ = false

instance GOrderable f b => GOrderable (M1 i c f) b where
  M1 x <?#  M1 y = x <?#  y
  M1 x <=?# M1 y = x <=?# y

instance Orderable a b => GOrderable (K1 i a) b where
  K1 a <?#  K1 b = a <?  b
  K1 a <=?# K1 b = a <=? b

-- Boring instances that end up being useful when deriving Orderable with Generics

instance Boolean b => Orderable () b where
  _ <?  _ = false
  _ <=? _ = true
instance Boolean b => Orderable Void b where
  x <?  y = x `seq` y `seq` error "Orderable[Void].<?"
  x <=? y = x `seq` y `seq` error "Orderable[Void].<=?"
instance Boolean b => Orderable Int b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Integer b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Natural b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Word b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Word8 b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Word16 b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Word32 b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Word64 b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Int8 b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Int16 b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Int32 b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Int64 b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Char b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Float b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Double b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Ordering b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
instance Boolean b => Orderable Bool b where
  x <?  y = bool (x <  y)
  x <=? y = bool (x <= y)
