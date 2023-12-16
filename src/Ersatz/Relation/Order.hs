{-# LANGUAGE OverloadedLists #-}
-- | This module defines properties of order-theoretic relations and properties
-- of elements described by an ordered structure.
--
-- == Goals
--
-- Many particular order structures you might be interested in testing or
-- asserting the existence of have multiple denotationally equivalent encodings,
-- but which encoding will be useful for specific data with a particular solver
-- and a particular set of parameters will probably not be /a priori/ clear.
--
-- This module is intended to facilitate the process of finding such encodings:
-- low-level properties are explicitly provided in a few variations, and a few
-- combinators are provided for generating such variations more easily.
--
-- There are also some example higher-level properties testing or asserting that
-- a relation is a particular kind of ordered structure (a preorder, a
-- semilattice, etc.), but they are by no means an exhaustive presentation of
-- encodings.
--
-- == Conventions
--
-- In the context of this module's documentation, an ordered structure
-- \( (A, R \subseteq A \times A )\) is given by
--
--  - a /carrier set/ \( A \)
--  - a binary relation \( R \) — typically denoted \( \le \).
--
-- Note that for want of concise alternative notation, \( \land \) and
-- \( \lor \) are used in this module's documentation to refer to /meet/ and
-- /join/ rather than logical conjunction and disjunction. For the logical
-- connectives, prose or /&/ and /|/ are used instead. This contrasts with the
-- rest of the package documentation.
--
-- Where a relation corresponds to what is conventionally treated as a function
-- (e.g. meet, join, pseudocomplement), this module follows the common logic
-- programming convention that the last argument represents the "output" of the
-- operation.

-- TODO summary:
-- 1. rebase for domain
--
-- 2. Test before submitting:
--      - atom, coatom
--      - absorption
--      - relativeComplement
--      - complement
--      - pseudocomplement
--      - meets_alwaysExist'
--      - joins_alwaysExist'
--      - complement_alwaysExists'
--      - complement_alwaysExists_with'
--      - pseudocomplement_alwaysExists'
--      - pseudocomplement_alwaysExists_with'
--      - relativeComplement_alwaysExists'

module Ersatz.Relation.Order
(
-- * Predicates of particular elements or subsets
  lte
, equiv
, gte
, lt
, gt
, lt'
, gt'
, btw
, strict_btw
, strict_btw'
, covers
, atom
, atom_with
, coatom
, coatom_with
, lowerClosure
, upperBound
, upperClosure
, least
, greatest
, minimal
, maximal
, leastWhere
, greatestWhere
, leastWhere'
, greatestWhere'
, minimalWhere
, maximalWhere
, minimalWhere'
, maximalWhere'
, bottom
, top
, glb
, lub
, glb'
, lub'
, meet
, join
, meet'
, join'
, complement
, complement_with
, complement'
, complement_with'
, pseudocomplement
, pseudocomplement_with
, pseudocomplement'
, pseudocomplement_with'
, relativeComplement
, relativeComplement'
-- ** Predicate combinators
-- |
-- Many of the predicates of particular elements (or pairs of elements, etc.)
-- test or assert that there exists at least one element in the universe of a
-- relation such that \( p(x)\), and often a variant may be desirable that tests
-- that there is a /unique/ element \( x \) in the universe of a relation such
-- that \( p(x) \).
--
-- If you write your own predicates of elements or subsets of an ordered
-- structure, you may wish to be able to succinctly define such variants of an
-- existing predicate. The combinators in this subsection facilitate this.
--
-- A simple example is the definition of @bottom :: Relation a a -> a -> Bit@ in
-- terms of @least :: Relation a a -> a -> Bit@:
--
-- >>> bottom = unique <*> least
--
-- Recall that for @(->)@, @\<*\>@ is the S-combinator:
--
-- >>> data A ; data B ; data C
-- >>> g = undefined :: A -> B -> C
-- >>> f = undefined :: A -> B
-- >>> :t g <*> f     -- (g <*> f) x == g x (f x)
-- g <*> f :: A -> C
-- >>> :t (<*>) @((->) A) @B @C
-- (<*>) @((->) A) @B @C :: (A -> (B -> C)) -> (A -> B) -> A -> C
--
-- Similarly, the predicate asserting that some element \( m \) is a meet
-- (greatest lower bound) of \( x \) and \( y \) in some set \(A \) with some
-- kind of order relation given by \( \le \) is
-- @meet :: Relation a a -> a -> a -> a -> Bit@; the variant asserting
-- that \( m \) is the /unique/ such element is defined as
--
-- >>> meet' = uniqueWith' <*> meet
--
, unique
, uniqueWith
, uniqueWith'
-- * Order-theoretic relation properties à la carte
-- |
-- This section contains properties that can be used
--
--   - As building blocks for properties asserting that a relation defines a
--     specific ordered structure.
--   - For explicitly asserting redundant information to a solver that may be
--     useful to assert even though it is entailed by other assertions.
, lowerBound_alwaysExists
, upperBound_alwaysExists
, least_exists
, greatest_exists
, bottom_exists
, top_exists
, meets_alwaysExist
, joins_alwaysExist
, meets_alwaysExist'
, joins_alwaysExist'
, meet_commutative
, join_commutative
, meet_associative
, join_associative
, meet_idempotent
, join_idempotent
, absorption
, complement_alwaysExists
, complement_alwaysExists_with
, complement_alwaysExists'
, complement_alwaysExists_with'
, pseudocomplement_alwaysExists
, pseudocomplement_alwaysExists_with
, pseudocomplement_alwaysExists'
, pseudocomplement_alwaysExists_with'
, relativeComplement_alwaysExists
, relativeComplement_alwaysExists'
, distributive_po
, distributive_po'
, distributive_lat
, distributive_lat'
, modular_lat
, upperBoundExists_implies_joinExists
, upperBoundExists_implies_joinExists'
-- * Properties asserting that a relation is a specific order structure
-- |
-- These are provided mostly for convenience and a starting point for
-- prototyping: for any particular context - especially ones where a relevant
-- order relation is relatively richly structured - there are often multiple
-- ways of expressing that a particular order structure holds, and it will
-- plausibly not be /a priori/ clear what is better for any particular use case
-- with respect to any particular solver, parameterization of a given solver, or
-- problem domain.
--
-- For example, there are many order structures structures that are
--
--   1. A join semilattice, a meet semilattice, or both.
--   2. Lower bounded, upper bounded, or both lower and upper bounded.
--   3. Distributive or complemented - or some other third property /p/ with
--      multiple equivalent ways of testing that /p/ holds (e.g. due to
--      algebraic identities).
--
-- There are multiple ways of testing/asserting that any one of these types
-- of properties holds, and hence many denotationally equivalent combinations
-- of assertions that will not - in general - permit compositional reasoning
-- about performance of a query or assertion to a degree that is useful.
--
-- Accordingly, the list of structures here stops short of enumerating more
-- elaborate structures with more than two ways to construct them in terms of
-- the relation properties above - e.g. various species of (semi)lattices.
, structureWhere
, preorder
, partial_order
, strict_partial_order
, strict_partial_order'
, total_order
, tolerance
, equivalence
, downward_directed
, upward_directed
, meet_semilattice
, join_semilattice
, meet_semilattice'
, join_semilattice'
, bounded
, lowerBounded_with
, upperBounded_with
, bounded_with
, bounded'
, lowerBounded_with'
, upperBounded_with'
, bounded_with'
)
where

import Prelude hiding
  ( (&&)
  , all
  , any
  , and
  , or
  , not
  , product
  )
import Data.Tuple
  ( swap
  )
import Control.Arrow
 ( (&&&)
 )
import Control.Applicative
  ( liftA2
  )
import Data.Composition
  ( (.:)
  )

import Ersatz.Bit
  ( Bit
  , Boolean ( all
            , any
            , and
            , not
            , (==>)
            , (&&)
            )
  )
import Ersatz.Equatable
  ( Equatable ( (===)
              , (/==)
              )
  )
import Ersatz.Counting
  ( exactly
  , atmost
  )
import Ersatz.Relation.Data
  ( Relation
  , (!)
  , universe
  )
import Ersatz.Relation.Prop
  ( symmetric
  , asymmetric
  , anti_symmetric
  , transitive
  , reflexive
  , irreflexive
  , total
  )

import Data.Ix
  ( Ix
  )
import Data.List.NonEmpty
  ( NonEmpty
  )



-- Helper function used in several places in the module

-- | Tests if a relation \( P \subseteq A \times A \) holds over the universe of
-- a binary relation \( R \subseteq A \times A \). This is useful for succinctly
-- defining properties of an order-theoretic structure — e.g. every pair of
-- elements has a (least) upper bound, etc.
forAllPairs :: ( Ix a ) => (a -> a -> Bit) -> Relation a a -> Bit
forAllPairs p =
  let pairs  = uncurry (liftA2 (,)) . (id &&& id)
  in  all (uncurry p) . pairs . universe


-- | Given a relation and a predicate @p :: a -> Bit@, this yields a new
-- predicate @p' :: a -> Bit@ that tests whether both @p@ holds of some @x@ and
-- whether @x@ is the only @a@ in the universe of a given relation where @p@
-- holds.
unique :: ( Ix a ) => Relation a a -> (a -> Bit) -> a -> Bit
unique r p x =
  p x && exactly 1 (p <$> universe r)

uniqueWith :: Ix a => Relation a a -> (b -> a -> Bit) -> b -> a -> Bit
uniqueWith r p = unique r . p

uniqueWith' :: Ix a => Relation a a -> (b -> c -> a -> Bit) -> b -> c -> a -> Bit
uniqueWith' r p = unique r .: p

-- | Tests/asserts that the provided operation (ternary relation) modeling what
-- is assumed to be a functional relation is commutative with respect to the
-- given collection of elements @ta@.
--
-- Formula size is cubic in the size of @ta@.
binOp_alwaysCommutative :: ( Ix a, Foldable t, Applicative t )
  => (a -> a -> a -> Bit)
  -> t a
  -> Bit
binOp_alwaysCommutative f ta =
  let pairs    = uncurry (liftA2 (,)) . (id &&& id)
      iff_ a b = (a ==> b) && (b ==> a)
      p (x,y)  = all (\z -> f x y z `iff_` f y x z)
                     ta
  in  all p $ pairs ta

-- | Tests/asserts that the provided operation (ternary relation) modeling what
-- is assumed to be a functional relation is idempotent with respect to the
-- given collection of elements @ta@ in the sense relevant to lattices:
--
--  1. \( a \lor  a = a \).
--  2. \( a \land a = a \).
--
-- Formula size is linear in the size of @ta@.
binOp_alwaysIdempotent :: ( Ix a, Foldable t )
  => (a -> a -> a -> Bit)
  -> t a
  -> Bit
binOp_alwaysIdempotent f ta =
  let p  x = f x x x
  in  all p ta

-- | Tests/asserts that the provided operation (ternary relation) modeling what
-- is assumed to be a functional relation is associative with respect to the
-- given collection of elements @as@.
binOp_alwaysAssociative :: ( Foldable t, Applicative t, Ix a, Equatable a )
  => (a -> a -> a -> Bit)
  -> t a
  -> Bit
binOp_alwaysAssociative f ta =
  let triples    as = (,,)  <$> as <*> as <*> as
      quadruples as = (,,,) <$> as <*> as <*> as <*> as
      -- x `f` (y `f` z) = (x `f` y) `f` z
      --    a      b     =     d      c
      lhs x y z b a =  f x b a
                    && f y z b
      rhs x y z d c =  f d z c
                    && f x y d
      p (x,y,z) = all (\(b,d,c,a) ->
                         lhs x y z b a && rhs x y z d c
                         ==> a === c)
                      (quadruples ta)
  in and $ p <$> triples ta



-- Basic order relations defined in terms of ≤, with a variants for partial
-- orders.

-- | Given a preorder \( (A, \le) \) and two elements, tests whether
-- \( x \le y \).
--
-- Does not test that \( \le \) defines a preorder.
lte :: ( Ix a ) => Relation a a -> a -> a -> Bit
lte r = (r !) .: (,)

-- | Given a preorder \( (A, \le) \) and two elements, tests whether
-- \( x \ge y \).
--
-- Does not test that \( \le \) defines a preorder.
gte :: ( Ix a ) => Relation a a -> a -> a -> Bit
gte r = (r !) .: (swap .: (,))

-- | Given a preorder \( (A, \le) \) and two elements
-- \( x, y \in A \), tests whether \( x \) and \( y \) are /equivalent/
-- under the preorder, i.e. whether \( x \le y \) and \( y \le x \).
--
-- If you have a /partial order/, you should consider using '==='
-- from "Ersatz.Equatable".
--
-- Does not test that \( \le \) defines a preorder.
equiv :: ( Ix a ) => Relation a a -> a -> a -> Bit
equiv r x y = lte r x y && lte r y x

-- | Given a preorder \( (A, \le) \) and two elements,
-- tests whether \( x \lt y \), defined as
-- \( x \lt y \iff x \le y \) and \( \neg (y \le x) \).
--
-- If you have a /partial order/, you should consider using 'lt''.
--
-- Does not test that \( \le \) defines a preorder.
lt :: ( Ix a ) => Relation a a -> a -> a -> Bit
lt r x y = lte r x y && not (lte r y x)

-- | Given a partial order \( (A, \le) \) and two
-- elements, tests whether \( x \lt y \), defined as
-- \( x \lt y \iff x \le y \) and \( y \neq x \).
--
-- Does not test that \( \le \) defines a partial order.
lt' :: ( Ix a, Equatable a ) => Relation a a -> a -> a -> Bit
lt' r x y = lte r x y && (y /== x)

-- | Given a preorder \( (A, \le) \) and two elements,
-- tests whether \( x \gt y \), defined as
-- \( x \gt y \iff x \ge y \) and \( \neg (y \ge x) \).
--
-- If you have a /partial order/, you should consider using 'gt''.
--
-- Does not test that \( \le \) defines a preorder.
gt :: ( Ix a ) => Relation a a -> a -> a -> Bit
gt r x y = gte r x y && not (gte r y x)

-- | Given a partial order \( (A, \le) \) and two
-- elements, tests whether \( x \gt y \), defined as
-- \( x \gt y \iff x \ge y \) and \( y \neq x \).
--
-- Does not test that \( \le \) defines a partial order.
gt' :: ( Ix a, Equatable a ) => Relation a a -> a -> a -> Bit
gt' r x y = gte r x y && (y /== x)

-- | Given a preorder \( (A, \le) \) and three elements
-- \( x, y, z \in A \), tests whether \( z \) is in the closed interval
-- \( [x,y] \), i.e. whether \( x \le y \le z \).
--
-- Does not test that \( \le \) defines a preorder.
btw :: ( Ix a ) => Relation a a -> a -> a -> a -> Bit
btw r x z = uncurry (&&)
          . (lte r x &&& lte r z)

-- | Given a preorder \( (A, \le) \) and three elements
-- \( x, y, z \in A \), tests whether \( z \) is in the open interval
-- \( (x,y) \), i.e. whether \( x \lt y \lt z \), where
-- \( \lt \) is the strict preorder relation induced by \( \le \) and its
-- associated notion of equivalence (see 'lt'):
--
-- Does not test that \( \le \) defines a preorder.
strict_btw :: ( Ix a ) => Relation a a -> a -> a -> a -> Bit
strict_btw r x z = uncurry (&&)
                 . (lt r x &&& lt r z)

-- | Given a partial order \( (A, \le) \) and three elements
-- \( x, y, z \in A \), tests whether \( x \lt y \lt z \), where
-- \( \lt \) is the strict partial order relation induced by \( \le \)
-- (see 'lt''):
--
-- Does not test that \( \le \) defines a partial order.
strict_btw' :: ( Ix a, Equatable a ) => Relation a a -> a -> a -> a -> Bit
strict_btw' r x z = uncurry (&&)
                  . (lt' r x &&& lt' r z)

-- | Given a partial order \( (A, \le) \) and two elements
-- \( y, x \in A \), \( y \) covers \( x \) iff
--
--   1. \( x \lt y \) (see 'lt'').
--   2. There is no \( z \) such that \( x \lt z \lt y \) (see 'strict_btw'').
--
-- Does not test that \( \le \) defines a partial order.
--
-- Formula size is linear in \( |A| \).
covers :: ( Ix a, Equatable a )
  => Relation a a
  -> a              -- ^ The covering element.
  -> a              -- ^ The covered element.
  -> Bit
covers r y x =
     lt' r x y
  && not (any (strict_btw' r x y)
              (universe r))

-- | Given a partial order \( (A, \le) \), \( a \in A \) is an atom iff it
-- covers the bottom element \( \bot \in A \).
--
-- Does not test that \( \le \) defines a partial order or that a bottom element
-- exists.
--
-- However, given that partial orders are the expected use case, @atom r x@ is
-- defined in terms of 'least' rather than 'bottom', and tests if there is
-- /at most 1/ \( b \in A \) such that \( b \) is a least element of @r@ and
-- \( x \) covers \( b \).
atom :: ( Ix a, Equatable a ) => Relation a a -> a -> Bit
atom r x =
  atmost 1 $ (\bot -> least r bot && atom_with bot r x)
             <$> universe r
  -- in  all (\bot -> bottom r bot ==> atom_with bot r x) (universe r)
-- Formula size is at least quadratic in \( |A| \).

-- | This variant of 'atom' permits specifying that a particular value is the
-- bottom element.
--
-- Formula size is linear in \( |A| \).
atom_with :: ( Ix a, Equatable a )
  => a             -- ^ The bottom element.
  -> Relation a a
  -> a             -- ^ The element (atom) that covers the bottom element.
  -> Bit
atom_with bot r x = covers r x bot

-- | Given a partial order \( (A, \le) \), \(a \in A \) is a coatom iff it is
-- covered by the top element \( \top \in A \).
--
-- Does not test that \( \le \) defines a partial order or that a top element
-- exists.
--
-- Given that partial orders are the expected use case, @coatom r x@ is defined
-- in terms of 'greatest' rather than 'top', and tests if there is /at most 1/
-- \( t \in A \) such that \( t \) is a greatest element of @r@ and \( x \)
-- covers \( t \).
coatom :: ( Ix a, Equatable a ) => Relation a a -> a -> Bit
coatom r x =
  atmost 1 $ (\top' -> greatest r top' && coatom_with top' r x)
             <$> universe r
  -- in  all (\top' -> top r top' ==> coatom_with top' r x) (universe r)
-- Formula size is at least quadratic in \( |A| \).

-- | This variant of 'coatom' permits specifying that a particular value is the
-- top element.
--
-- Formula size is linear in \( |A| \).
coatom_with :: ( Ix a, Equatable a )
  => a             -- ^ The top element.
  -> Relation a a
  -> a             -- ^ The element (atom) that is covered by the top element.
  -> Bit
coatom_with = flip covers



-- | Given an ordered structure \( (A, \le) \), a non-empty collection
-- \( N \subseteq A \), and a value \( l \), tests if \( l \) is a lower bound
-- of every element of \( N \).
--
-- Formula size is linear in \( |N| \).
lowerBound :: ( Ix a ) => Relation a a -> NonEmpty a -> a -> Bit
lowerBound r as = flip all as . lte r

-- | Given an ordered structure \( (A, \le) \), a non-empty collection
-- \( N \subseteq A \), and a value \( l \), tests if \( l \) is a lower bound
-- of some element of \( N \), i.e. if \( l \) is in the lower closure of
-- \( N \).
--
-- Formula size is linear in \( |N| \).
lowerClosure :: ( Ix a ) => Relation a a -> NonEmpty a -> a -> Bit
lowerClosure r as = flip any as . lte r

-- | Given an ordered structure \( (A, \le) \), a non-empty collection
-- \( N \subseteq A \), and a value \( u \), tests if \( u \) is an upper bound
-- of every element of \( N \).
--
-- Formula size is linear in \( |N| \).
upperBound :: ( Ix a ) => Relation a a -> NonEmpty a -> a -> Bit
upperBound r as = flip all as . gte r

-- | Given an ordered structure \( (A, \le) \), a non-empty collection
-- \( N \subseteq A \), and a value \( u \), tests if \( u \) is an upper bound
-- of some element of \( N \), i.e. if \( u \) is in the upper closure of
-- \( N \).
--
-- Formula size is linear in \( |N| \).
upperClosure :: ( Ix a ) => Relation a a -> NonEmpty a -> a -> Bit
upperClosure r as = flip any as . gte r



-- | Given a preorder \( (A, \le) \), test if a particular element /l/ is a
-- /least/ element i.e. if \( \forall x \in A, l \le x \).
--
-- Note that if \( \le \) defines a partial order, then \( A \) has
-- /at most \( 1 \)/ least element.
--
-- The assumption that the relation defines a preorder is not tested.
--
-- Formula size is linear in \( |A| \).
least :: ( Ix a ) => Relation a a -> a -> Bit
least r l =
  all (lte r l) $ universe r

-- | Given a preorder \( (A, \le) \), check if a particular element /g/ is a
-- /greatest/ element i.e. if \( \forall x \in A, x \le g \).
--
-- Note that if \( \le \) defines a partial order, then \( A \) has
-- /at most \( 1 \)/ greatest element.
--
-- The assumption that the relation defines a preorder is not tested.
--
-- Formula size is linear in \( |A| \).
greatest :: ( Ix a ) => Relation a a -> a -> Bit
greatest r g =
  all (gte r g) $ universe r

-- | Given a predicate \( p \) defining a subset \( S \subseteq A \) and a
-- preorder \( (A, \le) \), test if a particular element \( l \) is a /least/
-- element under \( \le \) among \( S \) i.e. if
-- \( l \in S \; \& \; \forall x \in S, l \le x \).
--
-- The assumption that the relation defines a preorder is not tested.
--
-- If the formula size of \( p(x) \) is \( m \), then the formula size here is
-- \( O(m \cdot |A|) \).
leastWhere :: ( Ix a ) => (a -> Bit) -> Relation a a -> a -> Bit
leastWhere p r l =
  p l && all (\x -> p x ==> lte r l x) (universe r)

-- | Given a predicate \( p \) defining a subset \( S \subseteq A \) and a
-- preorder \( (A, \le) \), check if a particular element /g/ is a /greatest/
-- element under \( \le \) among \( S \) i.e. if
-- \( g \in S \; \& \; \forall x \in S, x \le g \).
--
-- The assumption that the relation defines a preorder is not tested.
--
-- If the formula size of \( p(x) \) is \( m \), then the formula size here is
-- \( O(m \cdot |A|) \).
greatestWhere :: ( Ix a ) => (a -> Bit) -> Relation a a -> a -> Bit
greatestWhere p r g =
  p g && all (\x -> p x ==> gte r g x) (universe r)

-- | Variant of 'leastWhere' asserting that an element is the /unique/ least
-- element among the subset of the universe satisfying the given predicate.
leastWhere' :: ( Ix a ) => (a -> Bit) -> Relation a a -> a -> Bit
leastWhere' p = unique <*> leastWhere p

-- | Variant of 'greatestWhere' asserting that an element is the /unique/
-- greatest element among the subset of the universe satisfying the given
-- predicate.
greatestWhere' :: ( Ix a ) => (a -> Bit) -> Relation a a -> a -> Bit
greatestWhere' p = unique <*> greatestWhere p

-- | Given a preorder \( (A, \le) \), check if a particular element /m/ is a
-- /minimal/ element i.e. if \( \forall x \in A, x \le m \rightarrow m \le x \).
--
-- Note that every least element is a minimal element, but the reverse is not in
-- general true. Unlike a least element, a minimal element need not be
-- comparable to every element of \( A \).
--
-- An arbitrary preordered set may have any number of minimal elements or any
-- number of least elements, but if a preordered set \( A \) has at least one
-- least element, then every minimal element is also a least element.
--
-- If \( \le \) defines a partial order, then \( A \) may have \( 0 \) or more
-- minimal elements, but if it has more than one minimal element, it cannot have
-- a least element; if a partial order has a least element, that element must
-- also be the only least element and the only minimal element.
--
-- The assumption that the relation defines a preorder is not tested.
--
-- Formula size is linear in \( |N| \).
minimal :: ( Ix a ) => Relation a a -> a -> Bit
minimal r m =
  all (\x -> lte r x m ==> lte r m x) $ universe r

-- | Given a preorder \( (A, \le) \), check if a particular element /m/ is a
-- /maximal/ element i.e. if \( \forall x \in A, m \le x \rightarrow x \le m \).
--
-- Note that every greatest element is a maximal element, but the reverse is not
-- in general true. Unlike a greatest element, a maximal element need not be
-- comparable to every element of \( A \).
--
-- An arbitrary preordered set may have any number of maximal elements or any
-- number of greatest elements, but if a preordered set \( A \) has at least one
-- greatest element, then every maximal element is also a greatest element.
--
-- If \( \le \) defines a partial order, then \( A \) may have \( 0 \) or more
-- maximal elements, but if it has more than one maximal element, it cannot have
-- a greatest element; if a partial order has a greatest element, that element
-- must also be the only greatest element and the only maximal element.
--
-- The assumption that the relation defines a preorder is not tested.
--
-- Formula size is linear in \( |N| \).
maximal :: ( Ix a ) => Relation a a -> a -> Bit
maximal r m =
  all (\x -> gte r x m ==> gte r m x) $ universe r

-- | Given a predicate \( p \) defining a subset \( S \subseteq A \) and a
-- preorder \( (A, \le) \), check if a particular element /m/ is a /minimal/
-- element under \( \le \) among \( S \) i.e. if
-- \( \forall x \in S, x \le m \rightarrow m \le x \).
--
-- The assumption that the relation defines a preorder is not tested.
--
-- If the formula size of \( p(x) \) is \( m \), then the formula size here is
-- \( O(m \cdot |A|) \).
minimalWhere :: ( Ix a ) => (a -> Bit) -> Relation a a -> a -> Bit
minimalWhere p r m =
  p m && all (\x -> (p x && lte r x m) ==> lte r m x) (universe r)

-- | Given a predicate \( p \) defining a subset \( S \subseteq A \) and a
-- preorder \( (A, \le) \), check if a particular element /m/ is a /maximal/
-- element under \( \le \) among \( S \) i.e. if
-- \( \forall x \in S, m \le x \rightarrow x \le m \).
--
-- The assumption that the relation defines a preorder is not tested.
--
-- If the formula size of \( p(x) \) is \( m \), then the formula size here is
-- \( O(m \cdot |A|) \).
maximalWhere :: ( Ix a ) => (a -> Bit) -> Relation a a -> a -> Bit
maximalWhere p r m =
  p m && all (\x -> (p x && gte r x m) ==> gte r m x) (universe r)

-- | Variant of 'minimalWhere' asserting that an element is the /unique/ minimal
-- element among the subset of the universe satisfying the given predicate.
minimalWhere' :: ( Ix a ) => (a -> Bit) -> Relation a a -> a -> Bit
minimalWhere' p = unique <*> minimalWhere p

-- | Variant of 'maximalWhere' asserting that an element is the /unique/ maximal
-- element among the subset of the universe satisfying the given predicate.
maximalWhere' :: ( Ix a ) => (a -> Bit) -> Relation a a -> a -> Bit
maximalWhere' p = unique <*> maximalWhere p

-- | Given a preorder \( (A, \le) \), tests if a particular element /b/ is a
-- /least/ element and the /only/ such least element, i.e. is the
-- /bottom element/ \( \bot \).
--
-- Note that if \( (A, \le) \) defines a partial order and it has a least
-- element \b\, it follows that \b\ is the only least element, but it
-- nevertheless may still be useful to assert that a particular element is the
-- unique least element.
--
-- The assumption that the relation defines a preorder is not tested.
bottom :: ( Ix a ) => Relation a a -> a -> Bit
bottom = unique <*> least
-- Formula size is at least linear in \( |A| \).

-- | Given a preorder \( (A, \le) \), tests if a particular element /t/ is a
-- /greatest/ element and the only such greatest element, i.e. is the
-- /top element/ \( \top \).
--
-- Note that if \( (A, \le) \) defines a partial order and it has a greatest
-- element \t\, it follows that \t\ is the only greatest element, but it
-- nevertheless may still be useful to assert that a particular element is the
-- unique greatest element.
--
-- The assumption that the relation defines a preorder is not tested.
top :: ( Ix a ) => Relation a a -> a -> Bit
top = unique <*> greatest
-- Formula size is at least linear in \( |A| \).



-- | Given a preorder \( (A, \le) \) and a non-empty collection
-- \( N \subseteq A \), test if a particular element \( m \) is a greatest lower
-- bound (meet) of \( N \).
--
-- The assumption that the relation defines a preorder is not tested.
--
-- Formula size is \( O(|N| \cdot |A|) \).
glb :: ( Ix a ) => Relation a a -> NonEmpty a -> a -> Bit
glb r as = greatestWhere (lowerBound r as) r

-- | Given a preorder \( (A, \le) \) and a non-empty collection
-- \( N \subseteq A \), test if a particular element \( j \) is a least upper
-- bound (join) of \( N \).
--
-- The assumption that the relation defines a preorder is not tested.
--
-- Formula size is \( O(|N| \cdot |A|) \).
lub :: ( Ix a ) => Relation a a -> NonEmpty a -> a -> Bit
lub r as = leastWhere (upperBound r as) r

-- | Given a preorder \( (A, \le) \) and a non-empty collection
-- \( N \subseteq A \), check if a particular element \( m \) is the /unique/
-- greatest lower bound (meet) of \( N \).
--
-- The assumption that the relation defines a preorder is not tested.
glb' :: ( Ix a ) => Relation a a -> NonEmpty a -> a -> Bit
glb' = uniqueWith <*> glb

-- | Given a preorder \( (A, \le) \) and a non-empty collection
-- \( N \subseteq A \), check if a particular element \( j \) is the /unique/
-- least upper bound (join) of \( N \).
--
-- The assumption that the relation defines a preorder is not tested.
lub' :: ( Ix a ) => Relation a a -> NonEmpty a -> a -> Bit
lub' = uniqueWith <*> lub

-- | Variant of 'glb' for the common use case of meet/glb of just two elements.
--
-- Given a preorder \( (A, \le) \) and a pair of elements
-- \( x, y \in A \), check if a third element \( m \) is a /meet/ (greatest
-- lower bound) of \( x \) and \( y \), defined as
-- \( x \land y = j \iff x \le j \; \& \; y \le j \; \& \; \forall z \in A, x \le z \; \& \; y \le z \rightarrow j \le z \).
--
-- The assumption that the relation defines a preorder is not tested.
--
-- Formula size is \( O(|A|) \).
meet :: ( Ix a ) => Relation a a -> a -> a -> a -> Bit
meet r x y = glb r [x, y]

-- | Variant of 'lub' for the common use case of join/lub of just two elements.
--
-- Given a preorder \( (A, \le) \) and a pair of elements
-- \( x, y \in A \), check if a third element \( j \) is a /join/ (least upper
-- bound) of \( x \) and \( y \), defined as
-- \( x \lor y = j \iff x \le j \; \& \; y \le j \; \& \; \forall z \in A, x \le z \; \& \; y \le z \rightarrow j \le z \).
--
-- The assumption that the relation defines a preorder is not tested.
--
-- Formula size is \( O(|A|) \).
join :: ( Ix a ) => Relation a a -> a -> a -> a -> Bit
join r x y = lub r [x, y]

-- | Variant of 'glb'' for the common use case of meet/glb of just two elements.
--
-- Given a preorder \( (A, \le) \) and a pair of elements
-- \( x, y \in A \), check if a third element \( m \) is the unique /meet/
-- (greatest lower bound) of \( x \) and \( y \), where meet is defined as
-- \( x \land y = j \iff x \le j \; \& \; y \le j \; \& \; \forall z \in A, x \le z \; \& \; y \le z \rightarrow j \le z \).
--
-- The assumption that the relation defines a preorder is not tested.
meet' :: ( Ix a ) => Relation a a -> a -> a -> a -> Bit
meet' = uniqueWith' <*> meet

-- | Variant of 'lub'' for the common use case of join/lub of just two elements.
--
-- Given a preorder \( (A, \le) \) and a pair of elements \( x, y \in A \),
-- check if a third element \( j \) is the unique /join/ (least upper bound) of
-- \( x \) and \( y \), where join is defined as
-- \( x \lor y = j \iff x \le j \; \& \; y \le j \; \& \; \forall z \in A, x \le z \; \& \; y \le z \rightarrow j \le z \).
--
-- The assumption that the relation defines a preorder is not tested.
join' :: ( Ix a ) => Relation a a -> a -> a -> a -> Bit
join' = uniqueWith' <*> join



-- | Given an ordered structure \( (A, \le) \), check if one element of \( A \)
-- is a complement of another, where \( x \) is a complement of \( y \) iff
-- \( x ∨ y = \top \) and \( x ∧ y = \bot \), where \( \bot, \top \) are the
-- bottom and top elements (respectively); if neither the top element nor the
-- bottom element exist under \( \le \), then this formula will be unsatisfiable
-- for every pair of elements \( x, y \).
--
-- The assumption that the relation defines a particular kind of complemented
-- structure (e.g. a complemented lattice) is not tested, and neither are the
-- assumptions that bottom and top elements exist.
--
-- However, given the expected context of use (bounded lattices),
-- @complement r x y@ tests
--
--  1. If there is exactly 1 \( b \in A \) such that \( b \) is a least element
--     and \( x \land y = b \).
--  2. If there is exactly 1 \( t \in A \) such that \( t \) is a greatest
--     element and \( x \lor y = t \).
complement :: ( Ix a ) => Relation a a -> a -> a -> Bit
complement r =
  let law  (x,y) = exactly 1
                     ((\bot -> least r     bot
                            && meet  r x y bot)
                      <$> universe r)
      law' (x,y) = exactly 1
                     ((\top'-> greatest r     top'
                            && join     r x y top')
                      <$> universe r)
  in uncurry (&&) . (law &&& law') .: (,)
-- Formula size is at least quadratic in \( |A| \).

-- | This variant of 'complement' allows specifying that particular elements are
-- the bottom and top elements of the ordered structure, avoiding tests for such
-- elements.
--
-- Formula size is linear in \( |A| \).
complement_with :: ( Ix a )
  => a            -- ^ The bottom element.
  -> a            -- ^ The top element.
  -> Relation a a
  -> a
  -> a
  -> Bit
complement_with bot top' r =
  let law  (x,y) = join r x y bot
      law' (x,y) = meet r x y top'
  in  uncurry (&&) . (law &&& law') .: (,)

-- | Given an ordered structure \( (A, \le) \), check if one element of \( A \)
-- is the /unique/ complement of another, where \( x \) is a complement of
-- \( y \) iff \( x ∨ y = \bot \) and \( x ∧ y = \top \), where \( \bot, \top \)
-- are the bottom and top elements (respectively) under \( \le \); if neither the
-- top element nor the bottom element exist under \( \le \), then this formula
-- will be unsatisfiable for every pair of elements \( x, y \).
--
-- The assumption that the relation defines a particular kind of complemented
-- structure (e.g. a complemented lattice) is not tested, and neither are the
-- assumptions that bottom and top elements exist.
complement' :: ( Ix a ) => Relation a a -> a -> a -> Bit
complement' = uniqueWith <*> complement

-- | This variant of 'complement'' allows specifying that particular elements
-- are the bottom and top elements of the ordered structure, avoiding tests for
-- such elements.
complement_with' :: ( Ix a )
  => a            -- ^ The bottom element.
  -> a            -- ^ The top element.
  -> Relation a a
  -> a
  -> a
  -> Bit
complement_with' bot top' = uniqueWith <*> complement_with bot top'

-- | Given an ordered structure \( (A, \le) \) with bottom element \( 0 \) and a
-- value \( x \in A \), \( y \) is its pseudocomplement iff it is a greatest
-- \( z \in A \) such that \( x \land z = 0 \).
--
-- The assumption that the relation defines a particular kind of ordered
-- structure (at least a preorder) is not tested, nor is the assumption that a
-- bottom element exists.
--
-- However, pseudocomplements are typically defined in the context of a
-- structure that is at least a (semi)lattice, and hence a context where
-- least and greatest elements are unique.
--
-- Accordingly, given a relation \( \le \) and two elements \( x, y \), this
-- definition tests if there is exactly one \( b \in A \) such that \( b \) is a
-- least element under \( \le \) and \( y \) is a greatest element among all
-- \( z \in A \) such that \( x \land z = b \).
pseudocomplement :: ( Ix a )
  => Relation a a
  -> a            -- ^ The value with a pseudocomplement.
  -> a            -- ^ The pseudocomplement.
  -> Bit
pseudocomplement r x y =
  exactly 1 $
   (\bot -> least r bot
         && pseudocomplement_with bot r x y)
   <$> universe r
  -- all (\bot ->
  --        bottom r bot ==>
  --          pseudocomplement_with bot r x y)
  --          -- greatestWhere (p bot x) r y)
  --     (universe r)
-- Formula size is at least proportional to \( |A|^{3} \).

-- | This variant of 'pseudocomplement' allows specifying that a particular
-- element is the bottom element of the ordered structure, avoiding tests for
-- such an element.
--
-- Formula size is quadratic in \( |A| \).
pseudocomplement_with :: ( Ix a )
  => a            -- ^ The bottom element.
  -> Relation a a
  -> a            -- ^ The value with a pseudocomplement.
  -> a            -- ^ The pseudocomplement.
  -> Bit
pseudocomplement_with bot r x =
  greatestWhere (\z -> meet r x z bot) r

-- | This variant of 'pseudocomplement' asserts that a particular element \( y \)
-- is the /unique/ pseudocomplement of \( x \).
pseudocomplement' :: ( Ix a )
  => Relation a a
  -> a            -- ^ The value with a pseudocomplement.
  -> a            -- ^ The pseudocomplement.
  -> Bit
pseudocomplement' = uniqueWith <*> pseudocomplement

-- | This variant of 'pseudocomplement'' allows specifying that a particular
-- element is the bottom element of the ordered structure, avoiding tests for
-- such an element.
pseudocomplement_with' :: ( Ix a )
  => a            -- ^ The bottom element.
  -> Relation a a
  -> a            -- ^ The value with a pseudocomplement.
  -> a            -- ^ The pseudocomplement.
  -> Bit
pseudocomplement_with' bot = uniqueWith <*> pseudocomplement_with bot

-- | Given an order structure \( (A, \le) \) and four elements
-- \( b, t, x, y \in A \), tests whether \( x \) and \( y \) are relative
-- complements with respect to the closed interval \( [b, t] \) if \( x \) and
-- \( y \) are both between ('btw') \( b \) and \( t \).
--
-- Formula size is linear in \( |A| \).
relativeComplement :: ( Ix a )
  => a             -- ^ The bottom of the interval.
  -> a             -- ^ The top of the interval.
  -> Relation a a
  -> a
  -> a
  -> Bit
relativeComplement bot top' r x y =
  (btw r bot top' x && btw r bot top' y) ==> complement_with bot top' r x y

-- | Variant of 'relativeComplement' testing that a relative complement is
-- /unique/.
relativeComplement' :: ( Ix a )
  => a             -- ^ The bottom of the interval.
  -> a             -- ^ The top of the interval.
  -> Relation a a
  -> a
  -> a
  -> Bit
relativeComplement' bot top' = uniqueWith <*> relativeComplement bot top'



-- Properties an order structure may have.

-- | Tests if every pair of elements \( x, y \in A \) have a common lower bound
-- \( z \in A \) under the order structure \( (A, \le) \).
--
-- \( z \) is a lower bound of \( x \) and \( y \) iff both \( z \le x \) and
-- \( z \le y \).
--
-- Formula size is cubic in \( |A| \).
lowerBound_alwaysExists :: ( Ix a ) => Relation a a -> Bit
lowerBound_alwaysExists r =
  let p x y = any (lowerBound r [x,y]) (universe r)
  in forAllPairs p r

-- | Tests if every pair of elements \( x, y \in A \) have a common upper bound
-- \( z \in A \) under the order structure \( (A, \le) \).
--
-- \( z \) is an upper bound of \( x \) and \( y \) iff both \( x \le z \) and
-- \( y \le z \).
--
-- Formula size is cubic in \( |A| \).
upperBound_alwaysExists :: ( Ix a ) => Relation a a -> Bit
upperBound_alwaysExists r =
  let p x y  = any (upperBound r [x,y]) (universe r)
  in  forAllPairs p r

-- | Tests if there is at least one 'least' element in the universe of the given
-- order structure \( (A, \le) \).
--
-- Use 'least' to test whether a specific element is a least element.
--
-- Formula size is quadratic in \( |A| \).
least_exists :: ( Ix a ) => Relation a a -> Bit
least_exists =
  (any . least) <*> universe

-- | Tests if there is at least one 'greatest' element in the universe of the
-- given order structure \( (A, \le) \).
--
-- Use 'greatest' to test whether a specific element is a greatest element.
--
-- Formula size is quadratic in \( |A| \).
greatest_exists :: ( Ix a ) => Relation a a -> Bit
greatest_exists =
  (any . greatest) <*> universe

-- | Tests if there is exactly one 'least' element in the universe of the given
-- order structure \( (A, \le) \).
--
-- Use 'bottom' to test whether a specific element is the bottom element.
bottom_exists :: ( Ix a ) => Relation a a -> Bit
bottom_exists =
  exactly 1 . (fmap . least <*> universe)

-- | Tests if there is exactly one 'greatest' element in the universe of the
-- given order structure \( (A, \le) \).
--
-- Use 'top' to test whether a specific element is the top element.
top_exists :: ( Ix a ) => Relation a a -> Bit
top_exists =
  exactly 1 . (fmap . greatest <*> universe)

-- | Tests if every pair of elements in the universe of a given relation
-- \( (A, \le) \) have at least 1 'meet'.
--
-- Formula size is cubic in \( |A| \).
meets_alwaysExist :: ( Ix a ) => Relation a a -> Bit
meets_alwaysExist r =
  let p x y = any (meet r x y) (universe r)
  in  forAllPairs p r

-- | Tests if every pair of elements in the universe of a given relation
-- \( (A, \le) \) have exactly 1 'meet'.
meets_alwaysExist' :: ( Ix a ) => Relation a a -> Bit
meets_alwaysExist' r =
  let p x y = exactly 1 $ meet r x y <$> universe r
  in  forAllPairs p r

-- | Tests if every pair of elements in the universe of a given relation
-- \( (A, \le) \) have at least 1 'join'.
--
-- Formula size is cubic in \( |A| \).
joins_alwaysExist :: ( Ix a ) => Relation a a -> Bit
joins_alwaysExist r =
  let p x y = any (join r x y) (universe r)
  in  forAllPairs p r

-- | Tests if every pair of elements in the universe of a given relation
-- \( (A, \le) \) have exactly 1 'join'.
joins_alwaysExist' :: ( Ix a ) => Relation a a -> Bit
joins_alwaysExist' r =
  let p x y = exactly 1 $ join r x y <$> universe r
  in  forAllPairs p r

-- | Tests/asserts that the ternary functional relation modeling 'meet' induced
-- by the provided relation is commutative.
--
-- Even if this is entailed by other assertions, it may be helpful to explicitly
-- assert this.
meet_commutative :: ( Ix a ) => Relation a a -> Bit
meet_commutative =
  binOp_alwaysCommutative . meet <*> universe

-- | Tests/asserts that the ternary functional relation modeling 'join' induced
-- by the provided relation is commutative.
--
-- Even if this is entailed by other assertions, it may be helpful to explicitly
-- assert this.
join_commutative :: ( Ix a ) => Relation a a -> Bit
join_commutative =
  binOp_alwaysCommutative . join <*> universe

-- | Tests/asserts that the ternary functional relation modeling 'meet' induced
-- by the provided relation is associative.
--
-- Even if this is entailed by other assertions, it may be helpful to explicitly
-- assert this.
meet_associative :: ( Ix a, Equatable a ) => Relation a a -> Bit
meet_associative =
  binOp_alwaysAssociative . meet <*> universe

-- | Tests/asserts that the ternary functional relation modeling 'join' induced
-- by the provided relation is associative.
--
-- Even if this is entailed by other assertions, it may be helpful to explicitly
-- assert this.
join_associative :: ( Ix a, Equatable a ) => Relation a a -> Bit
join_associative =
  binOp_alwaysAssociative . join <*> universe

-- | Tests/asserts that the ternary functional relation modeling 'meet' induced
-- by the provided relation is idempotent in the sense associated with lattices:
--
--  1. \( a \lor  a = a \).
--  2. \( a \land a = a \).
--
-- Even if this is entailed by other assertions, it may be helpful to explicitly
-- assert this.
--
-- Formula size is linear in the size of the universe of the given relation.
meet_idempotent :: ( Ix a ) => Relation a a -> Bit
meet_idempotent =
  binOp_alwaysIdempotent . meet <*> universe

-- | Tests/asserts that the ternary functional relation modeling 'join' induced
-- by the provided relation is idempotent in the sense associated with lattices:
--
--  1. \( a \lor  a = a \).
--  2. \( a \land a = a \).
--
-- Even if this is entailed by other assertions, it may be helpful to explicitly
-- assert this.
--
-- Formula size is linear in the size of the universe of the given relation.
join_idempotent :: ( Ix a ) => Relation a a -> Bit
join_idempotent =
  binOp_alwaysIdempotent . join <*> universe

-- | For a lattice \( (A, \le) \), the absorption laws tie together meet and
-- join when each is considered as an associative, idempotent, and commutative
-- binary operation over \( A \): for all \( x, y, z \in A \)
--
--  1. \( x \land ( x \lor  y ) = x \).
--  2. \( x \lor  ( x \land y ) = x \).
--
-- This may follow from other assertions that \( (A, \le) \) is a lattice, but
-- may nevertheless be useful to redundantly assert as well.
absorption :: ( Ix a, Equatable a ) => Relation a a -> Bit
absorption r =
  let -- x ∧ (x ∨ y) = x
      --   c    d
      q_ x y d c = join r x y d ==> meet r x d c
      q' x y d   =   q_ x y d x
                  && exactly 1 (q_ x y d <$> universe r)
      q  x y     = all (q' x y)
                     $ universe r
      -- x ∨ (x ∧ y) = x
      --   a    b
      p_ x y b a = meet r x y b ==> join r x b a
      p' x y b   =  p_ x y b x
                 && exactly 1 (p_ x y b <$> universe r)
      p  x y     = all (p' x y)
                     $ universe r
  in  forAllPairs (\x y -> p x y && q x y) r


-- | Tests if every element in the universe of a given relation
-- \( (A, \le) \) has a 'complement'.
complement_alwaysExists :: ( Ix a ) => Relation a a -> Bit
complement_alwaysExists r =
  all (flip any (universe r) . complement r)
      (universe r)
-- Formula size is at least proportional to \( |A|^{4} \)

-- | Tests if every element in the universe of a given relation \( (A, \le) \)
-- has a 'complement_with', where the bottom and top elements are as specified.
complement_alwaysExists_with :: ( Ix a )
  => a             -- ^ The bottom element.
  -> a             -- ^ The top element.
  -> Relation a a
  -> Bit
complement_alwaysExists_with bot top' r =
  all (flip any (universe r) . complement_with bot top' r)
      (universe r)
-- Formula size is at least proportional to \( |A|^{3} \)

-- | Tests if every element in the universe of a given relation \( (A, \le) \)
-- has a unique 'complement'.
complement_alwaysExists' :: ( Ix a ) => Relation a a -> Bit
complement_alwaysExists' r =
  let p x = exactly 1 $ complement r x <$> universe r
  in  all p $ universe r

-- | Tests if every element in the universe of a given relation \( (A, \le) \)
-- has a unique 'complement_with', where the bottom and top elements are as
-- specified.
complement_alwaysExists_with' :: ( Ix a )
  => a             -- ^ The bottom element.
  -> a             -- ^ The top element.
  -> Relation a a
  -> Bit
complement_alwaysExists_with' bot top' r =
  let p x = exactly 1 $ complement_with bot top' r x <$> universe r
  in  all p $ universe r

-- | Tests if every element in the universe of a given relation \( (A, \le) \)
-- has a 'pseudocomplement'.
pseudocomplement_alwaysExists :: ( Ix a ) => Relation a a -> Bit
pseudocomplement_alwaysExists r =
  all (flip any (universe r) . pseudocomplement r)
      (universe r)
-- Formula size is at least proportional to \( |A|^{5} \).

-- | Tests if every element in the universe of a given relation \( (A, \le) \)
-- has a 'pseudocomplement_with', where the bottom element is as specified.
pseudocomplement_alwaysExists_with :: ( Ix a )
  => a             -- ^ The bottom element.
  -> Relation a a
  -> Bit
pseudocomplement_alwaysExists_with bot r =
  all (flip any (universe r) . pseudocomplement_with bot r)
      (universe r)
-- Formula size is at least proportional to \( |A|^{4} \).

-- | Tests if every element in the universe of a given relation \( (A, \le) \)
-- has a unique 'pseudocomplement'.
pseudocomplement_alwaysExists' :: ( Ix a ) => Relation a a -> Bit
pseudocomplement_alwaysExists' r =
  let p x = exactly 1 $ pseudocomplement r x <$> universe r
  in  all p $ universe r

-- | Tests if every element in the universe of a given relation \( (A, \le) \)
-- has a unique 'pseudocomplement_with', where the bottom element is as
-- specified.
pseudocomplement_alwaysExists_with' :: ( Ix a )
  => a             -- ^ The bottom element.
  -> Relation a a
  -> Bit
pseudocomplement_alwaysExists_with' bot r =
  let p x = exactly 1 $ pseudocomplement_with bot r x <$> universe r
  in  all p $ universe r

-- | Tests whether, for every closed interval \( [x,z] \) in the universe of a
-- given relation \( (A, \le) \), every \( z \) in the interval has at least one
-- 'relativeComplement' with respect to \( [x,z] \).
--
-- Formula size is \( O(|A|^5) \).
relativeComplement_alwaysExists :: ( Ix a ) => Relation a a -> Bit
relativeComplement_alwaysExists r =
  let p  bot top' x = any (relativeComplement bot top' r x) (universe r)
      p' bot top'   = lte r bot top' ==> all (p bot top') (universe r)
  in  forAllPairs p' r

-- | Tests whether, for every closed interval \( [x,z]\) in the universe of a
-- given relation \( (A, \le) \), every \( z \) in the interval has exactly 1
-- 'relativeComplement' with respect to \( [x,z] \).
relativeComplement_alwaysExists' :: ( Ix a ) => Relation a a -> Bit
relativeComplement_alwaysExists' r =
  let p  bot top' x = exactly 1 (relativeComplement bot top' r x <$> universe r)
      p' bot top'   = lte r bot top' ==> all (p bot top') (universe r)
  in  forAllPairs p' r


-- | Tests if, under the given partial order \( (A, \le) \), meet distributes over
-- join, i.e. whether
-- \( \forall x, y, z \in A, x \land (y \lor z) = (x \land y) \lor (x \land z) \).
--
-- Note that in an arbitrary partial order, meets and joins do not necessarily
-- exist, but - like any species of least or greatest element in a partial order
-- - if they exist, they are unique.
--
-- If \( \le \) defines a lattice, this distributive law is equivalent to
-- asserting that joins distribute over meets, however one may be a more useful
-- encoding for your domain than the other, depending on the nature of meet and
-- join definitions and other properties of your domain.
distributive_po :: ( Ix a ) => Relation a a -> Bit
distributive_po r =
  let -- TODO This is a straightforward encoding, but it is also horrendously
      -- large: are there alternatives in the SAT literature for encoding
      -- properties of operations like this?
      triples    as = (,,)  <$> as <*> as <*> as
      quadruples as = (,,,) <$> as <*> as <*> as <*> as
      -- x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z)
      --   a    b         d    c    e
      lhs x y z b a   =    meet r x b a
                        && join r y z b
      rhs x y z e d c =    join r d e c
                        && meet r x y d
                        && meet r x z e
      law (x,y,z)     = atmost 1 $
                          (\(b,e,d,w) ->
                              lhs x y z b w && rhs x y z e d w)
                          <$> (quadruples . universe $ r)
  in  all law (triples . universe $ r)
-- Formula size is at least proportional to \( O(|A|^8) \).

-- | Tests if, under the given partial order \( (A, \le) \), join distributes over
-- meet, i.e. whether
-- \( \forall x, y, z \in A, x \lor (y \land z) = (x \lor y) \land (x \lor z) \).
--
-- Note that in an arbitrary partial order, meets and joins do not necessarily
-- exist, but - like any species of least or greatest element in a partial order
-- - if they exist, they are unique.
--
-- If \( \le \) defines a lattice, this distributive law is equivalent to
-- asserting that meets distribute over joins, however one may be a more useful
-- encoding for your domain than the other, depending on the nature of meet and
-- join definitions and other properties of your domain.
distributive_po' :: ( Ix a ) => Relation a a -> Bit
distributive_po' r =
  let -- TODO This is a straightforward encoding, but it is also horrendously
      -- large: are there alternatives in the SAT literature for encoding
      -- properties of operations like this?
      triples    as = (,,)  <$> as <*> as <*> as
      quadruples as = (,,,) <$> as <*> as <*> as <*> as
      -- x ∨ (y ∧ z) = (x ∨ y) ∧ (x ∨ z)
      --   a    b         d    c    e
      lhs x y z b a   =    join r x b a
                        && meet r y z b
      rhs x y z e d c =    meet r d e c
                        && join r x y d
                        && join r x z e
      law (x,y,z)     = atmost 1 $
                          (\(b,e,d,w) ->
                              lhs x y z b w && rhs x y z e d w)
                          <$> (quadruples . universe $ r)
  in  all law (triples . universe $ r)
-- Formula size is at least proportional to \( O(|A|^8) \).

-- | Tests if, under the given ordered structure \( (A, \le) \), meet
-- distributes over join as one would expect in a lattice, i.e. whether
-- \( \forall x, y, z \in A, x \land (y \lor z) = (x \land y) \lor (x \land z) \)
-- and where every pair of elements has exactly one meet and exactly one join.
--
-- Given that \( \le \) defines a lattice, this distributive law is equivalent to
-- asserting that joins distribute over meets, however one may be a more useful
-- encoding for your domain than the other, depending on the nature of meet and
-- join definitions and other properties of your domain.
distributive_lat :: ( Ix a ) => Relation a a -> Bit
distributive_lat r =
  let -- TODO This is a straightforward encoding, but it is also horrendously
      -- large: are there alternatives in the SAT literature for encoding
      -- properties of operations like this?
      triples    as = (,,)  <$> as <*> as <*> as
      quadruples as = (,,,) <$> as <*> as <*> as <*> as
      -- x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z)
      --   a    b         d    c    e
      lhs x y z b a   =    meet r x b a
                        && join r y z b
      rhs x y z e d c =    join r d e c
                        && meet r x y d
                        && meet r x z e
      law (x,y,z)     = exactly 1 $
                          (\(b,e,d,w) ->
                              lhs x y z b w && rhs x y z e d w)
                          <$> (quadruples . universe $ r)
  in  all law (triples . universe $ r)
-- Formula size is at least proportional to \( O(|A|^8) \).

-- | Tests if, under the given ordered structure \( (A, \le) \), join
-- distributes over meet as one would expect in a lattice, i.e. whether
-- \( \forall x, y, z \in A, x \lor (y \land z) = (x \lor y) \land (x \lor z) \)
-- and where every pair of elements has exactly one meet and exactly one join.
--
-- Given that \( \le \) defines a lattice, this distributive law is equivalent to
-- asserting that meets distribute over joins, however one may be a more useful
-- encoding for your domain than the other, depending on the nature of meet and
-- join definitions and other properties of your domain.
distributive_lat' :: ( Ix a ) => Relation a a -> Bit
distributive_lat' r =
  let -- TODO This is a straightforward encoding, but it is also horrendously
      -- large: are there alternatives in the SAT literature for encoding
      -- properties of operations like this?
      triples    as = (,,)  <$> as <*> as <*> as
      quadruples as = (,,,) <$> as <*> as <*> as <*> as
      -- x ∨ (y ∧ z) = (x ∨ y) ∧ (x ∨ z)
      --   a    b         d    c    e
      lhs x y z b a   =    join r x b a
                        && meet r y z b
      rhs x y z e d c =    meet r d e c
                        && join r x y d
                        && join r x z e
      law (x,y,z)     = exactly 1 $
                          (\(b,e,d,w) ->
                              lhs x y z b w && rhs x y z e d w)
                          <$> (quadruples . universe $ r)
  in  all law (triples . universe $ r)
-- Formula size is at least proportional to \( O(|A|^8) \).

-- | Tests if the given lattice \( (A, \le) \) is /modular/, i.e. whether
-- \( \forall x, y, z \in A, x \le y \rightarrow x \lor (z \land y) = (x \lor z) \land y \).
--
-- Does not explicitly test that the given relation is a latttice, but the
-- definition does expect that every pair of elements has exactly \( 1 \) meet
-- and exactly \( 1 \) join.
modular_lat :: ( Ix a ) => Relation a a -> Bit
modular_lat r =
  let -- TODO This is a straightforward encoding, but it is also horrendously
      -- large: are there alternatives in the SAT literature for encoding
      -- properties of operations like this?
      -- x ∨ (z ∧ y) = (x ∨ z) ∧ y
      --   a    b         d    c
      triples    as = (,,)  <$> as <*> as <*> as
      lhs x y z b a =    join r x b a
                      && meet r z y b
      rhs x y z d c =    meet r d y c
                      && join r x z d
      law (x,y,z)   = exactly 1 $
                        (\(w,b,d) ->
                            lhs x y z w b && rhs x y z d w)
                          <$> (triples . universe $ r)
  in  all (\(x,y,z) -> lte r x y ==> law (x,y,z))
          (triples . universe $ r)
-- Formula size is at least proportional to \( O(|A|^7) \).


-- | Tests if the /upper bound property/ holds for a given order relation
-- \( (A, \le) \). The upper bound property holds iff for all \( x,y \in A \),
-- the existence of a common upper bound for \( \{x, y\} \) implies that
-- \( \{x,y\} \) have a /least/ upper bound (join).
--
-- Formula size is \( O(|A|^5) \).
upperBoundExists_implies_joinExists :: ( Ix a ) => Relation a a -> Bit
upperBoundExists_implies_joinExists r =
  let law x y = any (\u ->
                       upperBound r [x,y] u
                       ==> any (meet r x y)
                               (universe r))
                    (universe r)
  in  forAllPairs law r

-- | Variant of 'upperBoundExists_implies_joinExists' that tests whether the
-- existence of a common upper bound for some pair of elements implies the
-- existence of a /unique/ least upper bound (join).
upperBoundExists_implies_joinExists' :: ( Ix a ) => Relation a a -> Bit
upperBoundExists_implies_joinExists' r =
  let law x y = any (\u ->
                       upperBound r [x,y] u
                       ==> exactly 1 (meet r x y
                                      <$> universe r))
                    (universe r)
  in  forAllPairs law r
-- Formula size is at least proportional to \( O(|A|^5) \).



-- Types of order structures

-- | This combinator facilitates both succinct and /de/composable definitions of
-- more elaborate order structures. By defining larger predicates in terms of
-- data (a list of predicates) rather than a single opaque predicate, this can
-- also facilitate comparison of operationally different but denotationally
-- equivalent definitions that are permutations of some set of properties.
structureWhere :: ( Ix a ) => [Relation a a -> Bit] -> Relation a a -> Bit
structureWhere props = and . (props <*>) . pure

-- | A relation \( \approx \; \subseteq A \times A \) is a tolerance relation
-- iff it is reflexive and symmetric.
tolerance :: ( Ix a ) => [Relation a a -> Bit]

-- | A relation \( \equiv \; \subseteq A \times A \) is an equivalence relation
-- if it is reflexive, symmetric, and transitive.
equivalence :: ( Ix a ) => [Relation a a -> Bit]

-- | A relation \( \le \; \subseteq A \times A \) is a (non-strict) preorder
-- if it is reflexive and transitive.
preorder :: ( Ix a ) => [Relation a a -> Bit]

-- | A relation \( \lt \; \subseteq A \times A \) is a strict partial order
-- (i.e. a strict preorder), if it is irrreflexive and transitive, or
-- (equivalently) is asymmetric and transitive.
--
-- This function tests irreflexivity rather than asymmetry. One encoding vs. the
-- other may be more more useful in different contexts.
strict_partial_order :: ( Ix a ) => [Relation a a -> Bit]

-- | A relation \( \lt \; \subseteq A \times A \) is a strict partial order
-- (i.e. a strict preorder), if it is asymmetric and transitive, or
-- (equivalently) is irrreflexive and transitive.
--
-- This function tests asymmetry rather than irreflexivity. One encoding vs. the
-- other may be more more useful in different contexts.
strict_partial_order' :: ( Ix a ) => [Relation a a -> Bit]

-- | A relation \( \le \; \subseteq A \times A \) is a (non-strict) partial
-- order if it is reflexive, transitive, and antisymmetric.
--
-- Unless explicitly noted otherwise, "partial order" in this module means a not
-- necessarily strict partial order rather than a strict one.
partial_order :: ( Ix a ) => [Relation a a -> Bit]

-- | A relation \( \le \subseteq A \times A \) is a total order if it is
-- reflexive, transitive, antisymmetric, and total (strongly connected).
total_order :: ( Ix a ) => [Relation a a -> Bit]

tolerance     = [reflexive, symmetric]
equivalence   = [reflexive, symmetric, transitive]

preorder      = [reflexive, transitive]
partial_order = [reflexive, transitive, anti_symmetric]
total_order   = [reflexive, transitive, anti_symmetric, total]

strict_partial_order  = [irreflexive, transitive]
strict_partial_order' = [asymmetric , transitive]



-- | Tests if a relation \( (A, \le) \) defines a downward-directed set over its
-- universe, i.e. a preorder where every pair of elements has a lower bound.
downward_directed :: ( Ix a ) => [Relation a a -> Bit]
downward_directed = preorder ++ [lowerBound_alwaysExists]

-- | Tests if a relation \( (A, \le) \) defines an upward-directed set over its
-- universe, i.e. a preorder where every pair of elements has an upper bound.
upward_directed :: ( Ix a ) => [Relation a a -> Bit]
upward_directed = preorder ++ [upperBound_alwaysExists]

-- | Tests if a relation \( (A, \le) \) defines a meet-semilattice, i.e. a
-- partial order where every pair of elements has a greatest lower bound.
meet_semilattice :: ( Ix a ) => [Relation a a -> Bit]
meet_semilattice = partial_order ++ [meets_alwaysExist]

-- | Tests if a relation \( (A, \le) \) defines a join-semilattice, i.e. a
-- partial order where every pair of elements has a least upper bound.
join_semilattice :: ( Ix a ) => [Relation a a -> Bit]
join_semilattice = partial_order ++ [joins_alwaysExist]

-- | Variant of 'meet_semilattice' that also tests/asserts that meets are unique.
meet_semilattice' :: ( Ix a ) => [Relation a a -> Bit]
meet_semilattice' = partial_order ++ [meets_alwaysExist']

-- | Variant of 'join_semilattice' that also tests/asserts that joins are unique.
join_semilattice' :: ( Ix a ) => [Relation a a -> Bit]
join_semilattice' = partial_order ++ [joins_alwaysExist']

-- | Asserts that an unspecified least element and an unspecified greatest
-- element exist.
bounded :: ( Ix a ) =>  [Relation a a -> Bit]
bounded = [least_exists, greatest_exists]

lowerBounded_with :: ( Ix a ) => a -> [Relation a a -> Bit]
lowerBounded_with = pure . flip least

upperBounded_with :: ( Ix a ) => a -> [Relation a a -> Bit]
upperBounded_with = pure . flip greatest

bounded_with :: ( Ix a )
  => a  -- ^ A designated least element.
  -> a  -- ^ A designated greatest element.
  -> [Relation a a -> Bit]
bounded_with bot top' = [flip least bot, flip greatest top']

-- | Variant of 'bounded' that explicitly asserts that there is exactly 1 least
-- element and exactly 1 greatest element - i.e. a bottom element and a top
-- element.
bounded' :: ( Ix a ) =>  [Relation a a -> Bit]
bounded' = [bottom_exists, top_exists]

-- | Variant of 'lowerBounded_with' that explicitly asserts that there is
-- exactly 1 least element - i.e. a bottom element.
lowerBounded_with' :: ( Ix a ) => a -> [Relation a a -> Bit]
lowerBounded_with' = pure . flip bottom

-- | Variant of 'upperBounded_with' that explicitly asserts that there is
-- exactly 1 greatest element - i.e. a top element.
upperBounded_with' :: ( Ix a ) => a -> [Relation a a -> Bit]
upperBounded_with' = pure . flip top

bounded_with' :: ( Ix a )
  => a  -- ^ A designated bottom element.
  -> a  -- ^ A designated top element.
  -> [Relation a a -> Bit]
bounded_with' bot top' = [flip bottom bot, flip top top']

