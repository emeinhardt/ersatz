{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}
#if __GLASGOW_HASKELL__ >= 802
{-# LANGUAGE DerivingStrategies #-}
#endif

-- | This module represents symbolic subsets of a finite subset of some type @a@.
--
-- Internally it is currently @newtype Set a = Set { unSet :: Relation a () }@, and hence
-- under that is an @Array (a, ()) Bit@ — a unary encoding of a set as a bitmap.
--
-- Accordingly, most functions are calls to corresponding 'Data.Relation' operations;
-- see documentation there for formula sizes.
--
-- For the same reasons, if you expect to use both 'Ersatz.Relation' and 'Ersatz.Set' in
-- the same namespace, you will need to import them qualified or selectively hide
-- overlapping names.

module Ersatz.Relation.Set
  ( Set
   -- * Construction
  , set
  , build
  , buildFrom
  , buildFromM
  , universe'
  , empty
  , singleton

   -- * Concrete queries
  , bounds
  , indices
  , assocs
  , elems
  , universe
  , universeSize

   -- * Symbolic queries/assertions
  , (!)
  , member
  , card
  , subsetEq
  , subsetProper
  , disjoint
  , null

  -- * Operations
  , add
  , del

  -- ** Boolean operations
  , complement
  , union
  , intersection
  , difference
  , symmetric_difference

  -- ** Interfacing with 'Relation's
  , dom
  , img
  , toPartialRel

  ) where

import Prelude hiding
  ( null
  , not
  , and
  , (&&)
  , (||)
  , any
  )
import Data.Composition
  ( (.:)
  )
import Control.Arrow
  ( (***)
  , (&&&)
  , first
  )

import GHC.Generics
  ( Generic
  )
import Data.Coerce
  ( coerce
  )

import Ersatz.Solution
  ( Solution
  )
import Ersatz.Problem
  ( MonadSAT
  )
import Ersatz.Codec
  ( Codec ( Decoded
          , decode
          , encode
          )
  )
import Ersatz.Bit
  ( Bit
  , bool
  , true
  , false
  , any
  , not
  , and
  , (&&)
  , (||)
  )
import Ersatz.Bits
  ( Bits
  )
import Ersatz.Equatable
  ( Equatable
  , (===)
  , (/==)
  )
import qualified Ersatz.Relation.Op   as RO
import qualified Ersatz.Relation.Prop as RP
import qualified Ersatz.Relation.Data as RD
import Ersatz.Relation.Data
  ( Relation
  , relation
  , domain
  , codomain
  , domBounds
  , codBounds
  )

import qualified Data.Ix    as Ix
import qualified Data.Array as A
import Data.Array
  ( Array
  , Ix
  )


-- Helpers for shuffling between 'Set a' and 'Relation a ()' or components

pad :: a -> (a, ())
pad = (,())

unPad :: (a, ()) -> a
unPad = fst

relBounds_ :: (a,a) -> ((a, ()), (a, ()))
relBounds_ = pad *** pad

unRelBounds_ :: ((a, ()), (a, ())) -> (a,a)
unRelBounds_ = unPad *** unPad

relAssoc_ :: (a, b) -> ((a, ()), b)
relAssoc_ = first pad

unRelAssoc_ :: ((a, ()), b) -> (a, b)
unRelAssoc_ = first unPad

lift_ :: (a -> b) -> ((a, ()) -> b)
lift_ f = uncurry $ flip (const f)

relArray_ :: (Ix a) => Array a b -> Array (a, ()) b
relArray_ =
  uncurry A.array
  . (   relBounds_     . A.bounds
    &&& fmap relAssoc_ . A.assocs)

unRelArray_ :: (Ix a) => Array (a, ()) b -> Array a b
unRelArray_ =
  uncurry A.array
  . (   unRelBounds_     . A.bounds
    &&& fmap unRelAssoc_ . A.assocs)



-- Constructors

-- | @Set a@ represents a finite subset \( S \subseteq A \) of values of type
-- @a@.
newtype Set a = Set { unSet :: Relation a () }
#if __GLASGOW_HASKELL__ >= 802
  deriving stock Generic
#endif
#if __GLASGOW_HASKELL__ < 802
  deriving Generic
#endif

instance (Ix a) => Equatable (Set a) where
  r === s
    | bounds r /= bounds s = error "Relations don't have the same bounds!"
    | otherwise =
      and $ zipWith (===) (elems r) (elems s)
  r /== s = not $ r === s


instance (Ix a) => Codec (Set a) where
  type Decoded (Set a) = Array a Bool

  decode :: Ix a
    => Solution
    -> Set a
    -> Maybe (Decoded (Set a))
  decode sol = fmap unRelArray_ . decode sol . unSet

  encode :: Ix a
    => Array a Bool
    -> Set a
  encode = Set . encode . relArray_

-- | Using the provided bounds \( (a_{min}, a_{max}) \), construct a symbolic
-- Set \( S \subseteq A \) for the universe \( A = a_{min} \ldots a_{max} \).
set :: (Ix a, MonadSAT s m)
  => (a,a)
  -> m (Set a)
set = fmap Set . relation . relBounds_

-- | Construct a set \(S \subseteq A \) from a list.
build :: (Ix a)
  => (a,a)
  -> [(a,Bit)]
  -> Set a
build =
  Set
  . uncurry RD.build
  . (relBounds_ *** fmap relAssoc_)
  .: (,)

-- | Construct a set \(S \subseteq A \) from a predicate.
buildFrom :: (Ix a)
  => (a,a)
  -> (a -> Bit)
  -> Set a
buildFrom =
  Set
  . uncurry RD.buildFrom
  . (relBounds_ *** lift_)
  .: (,)

-- | Construct an indeterminate set \(S \subseteq A \) from a predicate.
buildFromM :: (Ix a, MonadSAT s m)
  => (a,a)
  -> (a -> m Bit)
  -> m (Set a)
buildFromM =
  fmap Set
  . uncurry RD.buildFromM
  . (relBounds_ *** lift_)
  .: (,)

-- | Construct a symbolic set \( \Omega \subseteq A \) from bounds where, by
-- construction, every element within the bounds is contained in the set.
universe' :: (Ix a) => (a,a) -> Set a
universe' =
  build
  <*> map (, true) . Ix.range

-- | Construct a symbolic set \( \varnothing \subseteq A \) from bounds where, by
-- construction, no elements are contained in the set.
empty :: (Ix a) => (a,a) -> Set a
empty =
  build
  <*> map (, false) . Ix.range

-- | Construct a symbolic set \( \{a\} \subseteq A \) from bounds where, by
-- construction, exactly one particular element \( a \) is contained in the set.
singleton :: (Ix a) => (a,a) -> a -> Set a
singleton bnd a =
  build bnd
  $ map (id &&& (bool . (a ==)))
        $ Ix.range bnd



-- Concrete queries

-- | The bounds of the array representing the set.
bounds :: (Ix a) => Set a -> (a,a)
bounds = unRelBounds_ . RD.bounds . coerce

-- | The list of indices of the array representing the set.
indices :: (Ix a) => Set a -> [a]
indices = fmap unPad . RD.indices . coerce

-- | The list of tuples for the given set \(S \subseteq A \), where the first
-- element is an index and the second element is a 'Bit' indicating whether the
-- element is contained in the represented set.
assocs :: (Ix a) => Set a -> [(a, Bit)]
assocs = fmap unRelAssoc_ . RD.assocs . coerce

-- | The list of elements of the array that represents the given set.
elems :: (Ix a) => Set a -> [Bit]
elems = RD.elems . coerce

-- | Synonym for 'indices', provided for parallelism with 'Data.Relation'.
universe :: (Ix a) => Set a -> [a]
universe = RD.domain . coerce

-- | The size of the universe that a symbolic (sub)set is a subset of.
universeSize :: (Ix a) => Set a -> Int
universeSize = A.rangeSize . bounds



-- Symbolic queries/assertions

-- | The number of elements \( |S| \) contained in the given symbolic subset
-- \( S \subseteq A \).
card :: (Ix a) => Set a -> Bits
card = RD.card . coerce

-- | @s ! a@ tests if \( a \in S \).
(!) :: (Ix a) => Set a -> a -> Bit
(!) =
  uncurry (RD.!)
  . (coerce *** pad)
  .: (,)

-- | Flipped, non-infix synonym for '!'.
member :: (Ix a) => a -> Set a -> Bit
member = flip (!)

-- | Tests if the set is empty.
null :: (Ix a) => Set a -> Bit
null = RP.empty . coerce

-- | @s \`subsetEq\` r@ tests if \( S \subseteq R \).
subsetEq :: (Ix a) => Set a -> Set a -> Bit
subsetEq =
  uncurry RP.implies
  . (coerce *** coerce)
  .: (,)

-- | @s \`subsetProper\` r@ tests if \( S \subset R \).
subsetProper :: (Ix a) => Set a -> Set a -> Bit
subsetProper = not . null .: difference

-- | @s \`disjoint\` r@ tests if \( S \cap R = \varnothing \).
disjoint :: (Ix a) => Set a -> Set a -> Bit
disjoint = null .: intersection



-- Operations

-- | Given a set \( S \subseteq A \) and an element \( a \), construct
-- a new set \( S \cup \{a\} \).
add :: (Ix a) => Set a -> a -> Set a
add s a
  | not (bounds s `Ix.inRange` a) = error "Element out of bounds of the set!"
  | otherwise = buildFrom (bounds s)
                          (\x -> bool (x == a) || x `member` s)

-- | Given a set \( S \subseteq A \) and an element \( a \), construct
-- a new set \( S \setminus \{a\} \).
del :: (Ix a) => Set a -> a -> Set a
del s a
  | not (bounds s `Ix.inRange` a) = error "Element out of bounds of the set!"
  | otherwise = buildFrom (bounds s)
                          (\x -> bool (x /= a) && x `member` s)

-- | Given a subset \( S \subseteq \Omega \) drawn form some finite universe
-- \( \Omega \subset A \), construct the complement of \( S \) with respect to
-- \( \Omega \), i.e. \( \Omega \setminus S \).
complement :: (Ix a) => Set a -> Set a
complement =
  Set
  . RO.complement
  . coerce

-- | Construct the union \( S \cup R \) of the two provided sets.
union :: (Ix a) => Set a -> Set a -> Set a
union =
  Set
  . uncurry RO.union
  . (coerce *** coerce)
  .: (,)

-- | Construct the intersection \( S \cap R \) of the two provided sets.
intersection :: (Ix a) => Set a -> Set a -> Set a
intersection =
  Set
  . uncurry RO.intersection
  . (coerce *** coerce)
  .: (,)

-- | Construct the difference \( S \setminus R \) of the two provided sets.
difference :: (Ix a) => Set a -> Set a -> Set a
difference =
  Set
  . uncurry RO.difference
  . (coerce *** coerce)
  .: (,)

-- | Construct the symmetric difference
-- \( (S \setminus R) \cup (R \setminus S) \) of the two provided sets.
symmetric_difference :: (Ix a) => Set a -> Set a -> Set a
symmetric_difference =
  Set
  . uncurry RO.symmetric_difference
  . (coerce *** coerce)
  .: (,)



-- Interfacing Relation values and Set values

-- | Construct a set representing the domain of definition of a 'Relation'.
dom :: (Ix a, Ix b) => Relation a b -> Set a
dom r =
  let in_dom_def x = any ((r RD.!) . (x,))
                         $ codomain r
  in  buildFrom (domBounds r) in_dom_def

-- | Construct a set representing the image of the domain of definition of a
-- 'Relation'.
img :: (Ix a, Ix b) => Relation a b -> Set b
img r =
  let in_cod_def y = any ((r RD.!) . (,y))
                         $ domain r
  in  buildFrom (codBounds r) in_cod_def

-- | Given a 'Set' \( S \subseteq A \), construct the corresponding partial
-- 'Relation' \( R \subseteq A \times A \) by restricting the 'identity'
-- relation on \( A \) to \( S \).
toPartialRel :: (Ix a) => Set a -> Relation a a
toPartialRel s =
  let dup                 = id &&& id
      homRelBounds_       = (dup *** dup) . bounds $ s
      p             (x,y) = x `member` s && bool (x == y)
  in  RD.buildFrom homRelBounds_ p
