{-# LANGUAGE ScopedTypeVariables #-}
module Ersatz.Relation.Prop

( 
-- * Properties
  implies
, symmetric
, asymmetric
, anti_symmetric
, transitive
, irreflexive
, reflexive
, regular
, regular_in_degree
, regular_out_degree
, max_in_degree
, min_in_degree
, max_out_degree
, min_out_degree
, empty
, complete
, total
, disjoint
, transitive_reduction_of
)

where

import Prelude hiding ( all, any, and, or, not, (&&), (||), product )
import Data.Composition ((.:))
import Control.Arrow ( (&&&), (***) )
import Data.Functor ( (<&>) )
import Control.Applicative ( liftA2 )

import Ersatz.Bit
import Ersatz.Relation.Data
import Ersatz.Relation.Op
import Ersatz.Counting
import Ersatz.Equatable ( Equatable, (===), (/==) )

import Data.Ix


instance (Ix a, Ix b) => Equatable (Relation a b) where
  r === s = and [implies r s, implies s r]
  r /== s = not $ r === s

-- | Given two relations \( R, S \subseteq A \times B \), check if \(R\) is a subset of \(S\).
implies :: ( Ix a, Ix b )
        => Relation a b -> Relation a b -> Bit
implies r s 
  | bounds r == bounds s = and $ do
      i <- indices r
      return $ (r ! i) ==> (s ! i)
  | otherwise = error "Relations don't have the same bounds!"

-- | Tests if a relation is empty, i.e., the relation doesn't contain any elements.
empty ::  ( Ix a, Ix b )
        => Relation a b -> Bit
empty r = and $ do
    i <- indices r
    return $ not $ r ! i

-- | Tests if a relation \( R \subseteq A \times B \) is complete,
-- i.e., \(R = A \times B \).
complete :: (Ix a, Ix b) => Relation a b -> Bit
complete r = empty $ complement r

-- | Tests if a relation \( R \subseteq A \times A \) is strongly connected, i.e.,
-- \( R \cup R^{-1} = A \times A \).
total :: ( Ix a ) => Relation a a -> Bit
total r = complete $ symmetric_closure r

-- | Tests if two relations are disjoint, i.e., 
-- there is no element that is contained in both relations.
disjoint :: (Ix a, Ix b) => Relation a b -> Relation a b -> Bit
disjoint r s = empty $ intersection r s

-- | Tests if a relation \( R \subseteq A \times A \) is symmetric,
-- i.e., \( R \cup R^{-1} = R \).
symmetric :: ( Ix a ) => Relation a a -> Bit
symmetric r = implies r ( mirror r )

-- | Tests if a relation \( R \subseteq A \times A \) is asymmetric,
-- i.e., \( \forall x, y \in A: ((x,y) \in R) \rightarrow ((y,x) \notin R) \).
asymmetric :: ( Ix a ) => Relation a a -> Bit
asymmetric r = implies r (complement (mirror r))

-- | Tests if a relation \( R \subseteq A \times A \) is antisymmetric,
-- i.e., \( R \cap R^{-1} \subseteq R^{0} \).
anti_symmetric :: ( Ix a ) => Relation a a -> Bit
anti_symmetric r = implies (intersection r (mirror r)) (identity (bounds r))

-- | Tests if a relation \( R \subseteq A \times A \) is transitive, i.e.,
-- \( \forall x, y \in A: ((x,y) \in R) \land ((y,z) \in R) \rightarrow ((x,z) \in R) \).
transitive :: ( Ix a )
           => Relation a a -> Bit
transitive r = implies (product r r) r

-- | Tests if a relation \( R \subseteq A \times A \) is irreflexive, i.e.,
-- \( R \cap R^{0} = \emptyset \).
irreflexive :: ( Ix a ) => Relation a a -> Bit
irreflexive r = empty $ intersection (identity $ bounds r) r

-- | Tests if a relation \( R \subseteq A \times A \) is reflexive, i.e.,
-- \( R^{0} \subseteq R \).
reflexive :: ( Ix a ) => Relation a a -> Bit
reflexive r = implies (identity $ bounds r) r

-- | Given an 'Int' \( n \) and a relation \( R \subseteq A \times B \), check if
-- \( \forall x \in A: | \{ (x,y) \in R \} | = n \) and
-- \( \forall y \in B: | \{ (x,y) \in R \} | = n \) hold.
regular :: (Ix a, Ix b) => Int -> Relation a b -> Bit

-- | Given an 'Int' \( n \) and a relation \( R \subseteq A \times B \), check if
-- \( \forall y \in B: | \{ (x,y) \in R \} | = n \) holds.
regular_in_degree :: (Ix a, Ix b) => Int -> Relation a b -> Bit

-- | Given an 'Int' \( n \) and a relation \( R \subseteq A \times B \), check if
-- \( \forall x \in A: | \{ (x,y) \in R \} | = n \) holds.
regular_out_degree :: (Ix a, Ix b) => Int -> Relation a b -> Bit

-- | Given an 'Int' \( n \) and a relation \( R \subseteq A \times B \), check if
-- \( \forall y \in B: | \{ (x,y) \in R \} | \leq n \) holds.
max_in_degree :: (Ix a, Ix b) => Int -> Relation a b -> Bit

-- | Given an 'Int' \( n \) and a relation \( R \subseteq A \times B \), check if
-- \( \forall y \in B: | \{ (x,y) \in R \} | \geq n \) holds.
min_in_degree :: (Ix a, Ix b) => Int -> Relation a b -> Bit

-- | Given an 'Int' \( n \) and a relation \( R \subseteq A \times B \), check if
-- \( \forall x \in A: | \{ (x,y) \in R \} | \leq n \) holds.
max_out_degree :: (Ix a, Ix b) => Int -> Relation a b -> Bit

-- | Given an 'Int' \( n \) and a relation \( R \subseteq A \times B \), check if
-- \( \forall x \in A: | \{ (x,y) \in R \} | \geq n \) holds.
min_out_degree :: (Ix a, Ix b) => Int -> Relation a b -> Bit

regular deg r = and [ regular_in_degree deg r, regular_out_degree deg r ]

regular_out_degree = out_degree_helper exactly
max_out_degree = out_degree_helper atmost
min_out_degree = out_degree_helper atleast
regular_in_degree deg r = regular_out_degree deg $ mirror r
max_in_degree deg r = max_out_degree deg $ mirror r
min_in_degree deg r = min_out_degree deg $ mirror r

out_degree_helper ::
  (Boolean b, Ix b1, Ix a) =>
  (t -> [Bit] -> b) -> t -> Relation a b1 -> b
out_degree_helper f deg r = and $ do
    let ((a,b),(c,d)) = bounds r
    x <- range ( a , c )
    return $ f deg $ do
        y <- range (b,d)
        return $ r ! (x,y)

-- | @transitive_reduction_of r s@ tests whether \(R \subseteq A \times A \) is
-- the transitive reduction of \(S \subseteq A \times A \), i.e. if \( S \) is
-- the smallest relation whose transitive closure \( S^{+} \) is identical to
-- that of \( R \).
--
-- This tests that \( S^{+} = R^{+} \), but does not also directly test that
-- there is no \( T \subseteq A \times A \) smaller than \( S \) with the same
-- transitive closure as \( R \): that is a property that is expensive to verify
-- when correct. Instead, this also tests that certain constraints hold for every
-- \( (x, y) \in S \) which are only true of transitive reductions.
--
-- Before stating those constraints, note that \( R, S \) can be interpreted
-- as directed graphs, and that while the transitive reduction of a directed
-- /acyclic/ graph (i.e. one where the reachability relation is a partial order)
-- is unique (and given by the covering relation associated with the reachability
-- relation), in the general case, the transitive reduction of an arbitrary
-- \( R \) is not uniquely defined.
--
-- This definition uses two types of constraints on edges that any transitive reduction
-- \( S \) of \( R \) must satisfy:
--
--   - one type ensures the number of edges in \( S \) /within/ strongly connected
--     components of \( R \) is minimal
--   - The other ensures that the number of edges /between/ strongly connected
--     components is minimal.
--
--  Altogether then, \( S \) is a transitive reduction of \( R \) iff:
--
--   1. \( S^{+} = R^{+} \).
--   2. \( S \subseteq R \).
--   3. For each set of vertices in a strongly connected component of
--      \( R^{+} \), there is a directed cycle in \( S \) among those
--      vertices.
--   4. For any two sets of vertices defining distinct strongly connected components
--      \( X \subset A \), \( Z \subseteq A \) where \( Z \) is reachable from \( X \):
--
--        - There is at most one edge in \( S \) from \( X \) to \( Z \).
--        - There is no edge iff there is any distinct third strongly
--          connected component \( Y \subseteq A \) where the vertices of \( Y \)
--          are reachable from \( X \) and the vertices of \( Z \) are reachable
--          from \( Y \).
transitive_reduction_of :: forall a. ( Ix a, Equatable a )
  => Relation a a
  -> Relation a a
  -> Bit
transitive_reduction_of tr r =
    let
       -- TODO Remove after #78 is merged
       domain_ = range . (fst *** fst) . bounds

       pairs :: (Applicative f) => f a -> f (a,a)
       pairs = uncurry (liftA2 (,)) . (id &&& id)

       -- True iff there is exactly 1 b ∈ bs s.t. p b.
       existsUnique :: [b] -> (b -> Bit) -> Bit
       existsUnique = exactly 1 .: (<&>)

       -- True iff p x and there is at most 1 y ∈ ys such that p y.
       -- Does not check whether x ∈ ys. (Not relevant in this local context.)
       isThe :: (Equatable b) => [b] -> (b -> Bit) -> b -> Bit
       isThe ys p x = p x && existsUnique ys p

       mutuallyReachable s x y = s ! (x,y) &&      s ! (y,x)
       oneWay            s x y = s ! (x,y) && not (s ! (y,x))

       universe_  = domain_             r
       closure_r  = transitive_closure  r

       -- An SCC is trivial iff it consists of a single vertex
       -- and that vertex has no path to itself.
       sameNontrivialScc :: a -> a -> Bit
       sameNontrivialScc = mutuallyReachable closure_r

       -- A singleton SCC is a non-trivial SCC that consists of a single vertex.
       singletonScc :: a -> Bit
       singletonScc = existsUnique universe_ . sameNontrivialScc

       -- True iff
       --   - x and y are in the same SCC.
       --   - x is the unique predecessor of y and y is the unique successor of
       --     x in the directed cycle of their common SCC.
       pred_ :: a -> a -> Bit
       -- The first term in the xor here is redundant with the other, but
       -- empirically seems useful to include for performance.
       -- The `xor` also entails that the second term can only be satisfied
       -- when x /= y.
       pred_ x y =  (   singletonScc x && x === y)
                 `xor`
                    (  isThe universe_  -- x is the unique element in y's SCC
                             (\z ->     -- preceding y in tr.
                                sameNontrivialScc x z
                             && tr ! (z,y))
                             x
                    && isThe universe_  -- y is the unique element in x's SCC
                             (\z ->     -- succeeding x in tr.
                                sameNontrivialScc x z
                             && tr ! (x,z))
                             y)

       -- The 'sameNontrivialScc' check is redundant with pred_;
       -- including it may help and doesn't seem to hurt.
       sccEdge      x y =    sameNontrivialScc x y
                          && pred_             x y
       interSccEdge x z =    oneWay closure_r  x z    -- This entails that
                                                      -- the scc of x /= the scc
                                                      -- of z.
                          && atmost 0 (   universe_   -- There is no distinct
                                      <&> (\y ->      -- third SCC 'between' those of
                                                      -- x and z.
                                             oneWay closure_r x y
                                          && oneWay closure_r y z))
                          && isThe (pairs universe_)  -- (x,z) is the only edge
                                   (\(u,v) ->         -- directly connecting the
                                         tr ! (u,v)   -- respective SCCs of x+z.
                                      && sameNontrivialScc x u
                                      && sameNontrivialScc z v)
                                   (x,z)

       in   all (\(x,y) ->
                tr ! (x,y)
                ==> (  r ! (x,y)
                    && (interSccEdge x y `xor` sccEdge x y)))
             (pairs universe_)
          && closure_r === transitive_closure tr
