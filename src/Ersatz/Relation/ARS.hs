module Ersatz.Relation.ARS
  ( -- * Abstract rewriting
    terminating, assertTerminating
  , peak, valley
  , locallyConfluent
  , confluent, semiconfluent
  , convergent, assertConvergent
  , pointSymmetric
  , relativeTo
  , connected
  , isNF
  , nfProperty
  , uniqueNFs, uniqueNFsReduction
  ) where

import Prelude hiding ( (&&), not, or, and, all, product )

import Control.Monad (guard)

import Data.Ix

import Ersatz.Bit
import Ersatz.Equatable
import Ersatz.Problem (MonadSAT)

import Ersatz.Relation.Data
import Ersatz.Relation.Op
import Ersatz.Relation.Prop



-- | Tests if a relation \( R \subseteq A \times A \) is terminating, i.e., 
-- there is no infinite sequence \( x_1, x_2, ... \) with \( x_i \in A \)
-- such that \( (x_i, x_{i+1}) \in R \) holds.
--
-- Formula size: linear in \( |A|^3 \)
terminating :: Ix a => Relation a a -> Bit
terminating = irreflexive . transitiveClosure

-- | Monadic version of 'terminating'. 
--
-- Note that @assert_terminating@ cannot be used for expressing non-termination
-- of a relation, only for expressing termination.
--
-- Formula size: linear in \( |A|^3 \)
--
-- ==== __Example__
--
-- @
-- example = do
--   result <- 'Ersatz.Solver.solveWith' 'Ersatz.Solver.Minisat.minisat' $ do
--     r <- 'relation' ((0,0),(2,2))
--     'Ersatz.Bit.assert' $ 'Ersatz.Counting.atleast' 3 $ 'elems' r
--     'assertTerminating' r
--     return r
--   case result of
--     (Satisfied, Just r) -> do putStrLn $ 'table' r; return True
--     _                   -> return False
-- @
assertTerminating :: (Ix a, MonadSAT s m) => Relation a a -> m ()
assertTerminating r = do
  s <- relation $ bounds r
  assert $ and [
      transitive s
    , irreflexive s
    , implies r s ]

-- | Constructs the peak \( R^{-1} \circ S \) of two relations
-- \( R, S \subseteq A \times A \).
--
-- Formula size: linear in \( |A|^3 \)
peak :: Ix a => Relation a a -> Relation a a -> Relation a a
peak r = product (mirror r)

-- | Constructs the valley \( R \circ S^{-1} \) of two relations
-- \( R, S \subseteq A \times A \).
-- 
-- Formula size: linear in \( |A|^3 \)
valley :: Ix a => Relation a a -> Relation a a -> Relation a a
valley r s = product r (mirror s)

-- | Tests if a relation \( R \subseteq A \times A \) is locally confluent, i.e.,
-- \( \forall a,b,c \in A: ((a,b) \in R) \land ((a,c) \in R) \rightarrow \exists d \in A: ((b,d) \in R^*) \land ((c,d)\in R^*) \).
--
-- Formula size: linear in \( |A|^3 \)
locallyConfluent :: Ix a => Relation a a -> Bit
locallyConfluent r =
  let r' = transitiveReflexiveClosure r
  in implies (peak r r) (valley r' r')

-- | Tests if a relation \( R \subseteq A \times A \) is confluent, i.e.,
-- \( \forall a,b,c \in A: ((a,b) \in R^*) \land ((a,c) \in R^*) \rightarrow \exists d \in A: ((b,d) \in R^*) \land ((c,d)\in R^*) \).
--
-- Formula size: linear in \( |A|^3 \)
confluent :: Ix a => Relation a a -> Bit
confluent r = 
  let r' = transitiveReflexiveClosure r
  in implies (peak r' r') (valley r' r')

-- | Tests if a relation \( R \subseteq A \times A \) is semi-confluent, i.e.,
-- \( \forall a,b,c \in A: ((a,b) \in R) \land ((a,c) \in R^*) \rightarrow \exists d \in A: ((b,d) \in R^*) \land ((c,d)\in R^*) \).
--
-- @semiconfluent@ is equivalent to 'confluent'.
--
-- Formula size: linear in \( |A|^3 \)
semiconfluent :: Ix a => Relation a a -> Bit
semiconfluent r =
  let r' = transitiveReflexiveClosure r
  in implies (peak r r') (valley r' r')

-- | Tests if a relation \( R \subseteq A \times A \) is convergent, i.e., 
-- \( R \) is 'terminating' and 'confluent'.
--
-- Formula size: linear in \( |A|^3 \)
convergent :: Ix a => Relation a a -> Bit
convergent r = terminating r && locallyConfluent r

-- | Monadic version of 'convergent'. 
--
-- Note that @assert_convergent@ cannot be used for expressing non-convergence
-- of a relation, only for expressing convergence.
--
-- Formula size: linear in \( |A|^3 \)
--
-- ==== __Example__
--
-- @
-- example = do
--   result <- 'Ersatz.Solver.solveWith' 'Ersatz.Solver.Minisat.minisat' $ do
--     r <- 'relation' ((0,0),(3,3))
--     'Ersatz.Bit.assert' $ 'Ersatz.Counting.exactly' 3 $ 'elems' r
--     'assertConvergent' r
--     'Ersatz.Bit.assert' $ 'Ersatz.Bit.not' $ 'transitive' r
--     return r
--   case result of
--     (Satisfied, Just r) -> do putStrLn $ 'table' r; return True
--     _                   -> return False
-- @
assertConvergent :: (Ix a, MonadSAT s m) => Relation a a -> m ()
assertConvergent r = do
  s <- relation $ bounds r
  t <- relation $ bounds r
  let u = universe r
      i = indices r
  assert $ and [
      transitive s
    , irreflexive s
    , implies r s
    , all (\x -> isNF x r ==> t ! (x,x)) u
    , all (\(x,y) -> s!(x,y) && t!(y,y) ==> t!(x,y)) i
    , nor $ do
        (x,y) <- i; z <- u; guard $ y /= z
        return $ t ! (x,y) && t ! (x,z) ]

-- | Tests if the matrix representation (i.e. the array) of a relation 
-- \( R \subseteq A \times A \) is point symmetric, i.e., for the matrix
-- representation
-- \( \begin{pmatrix} a_{11} & \dots & a_{1n} \\ \vdots & \ddots & \vdots \\ a_{n1} & \dots & a_{nn} \end{pmatrix} \)
-- holds \( a_{ij} = a_{(n-i+1)(n-j+1)} \).
pointSymmetric :: Ix a => Relation a a -> Bit
pointSymmetric r
  | isHomogeneous r = elems r === reverse (elems r)
  | otherwise = error "The domain must equal the codomain!"

-- | Given two relations \( R, S \subseteq A \times A \), 
-- construct
-- \( R \) relative to \( S \) defined by \( R/S = S^* \circ R \circ S^* \).
--
-- Formula size: linear in \( |A|^3 \)
relativeTo :: Ix a => Relation a a -> Relation a a -> Relation a a
r `relativeTo` s =
  let s' = transitiveReflexiveClosure s
  in foldl1 product [ s', r , s' ]

-- | Tests if a relation \( R \subseteq A \times A \) is connected, 
-- i.e., \( (R \cup R^{-1})^* = A \times A \).
--
-- Formula size: linear in \( |A|^3 \)
connected :: Ix a => Relation a a -> Bit
connected = complete . equivalenceClosure

-- | Given an element \( x \in A \) and a relation \( R \subseteq A \times A \), 
-- check if \( x \) is a normal form, i.e.,
-- \( \forall y \in A: (x,y) \notin R \).
--
-- Formula size: linear in \( |A| \)
isNF :: Ix a => a -> Relation a a -> Bit
isNF x r =
  let (b,d) = codBounds r
  in nor $ (r !) <$> range ((x,b),(x,d))

-- | Tests if a relation \( R \subseteq A \times A \) has the normal form
-- property, i.e., \( \forall a,b \in A \) holds: if \(b\) is a normal form and
-- \( (a,b) \in (R \cup R^{-1})^{*} \), then \( (a,b) \in R^{*} \).
--
-- Formula size: linear in \( |A|^3 \)
nfProperty :: Ix a => Relation a a -> Bit
nfProperty r = and $ do
  let trc = transitiveReflexiveClosure r
      ec  = equivalenceClosure r
  (x,y) <- indices r
  return $ (isNF y r && ec ! (x,y)) ==> trc ! (x,y)

-- | Tests if a relation \( R \subseteq A \times A \) has the unique normal form
-- property, i.e., \( \forall a,b \in A \) with \( a \neq b \) holds: if \(a\)
-- and \(b\) are normal forms, then \( (a,b) \notin (R \cup R^{-1})^{*} \).
--
-- Formula size: linear in \( |A|^3 \)
uniqueNFs :: Ix a => Relation a a -> Bit
uniqueNFs r = and $ do
  let ec = equivalenceClosure r
  (x,y) <- indices r
  guard $ x < y
  return $ (isNF x r && isNF y r) ==> not $ ec ! (x,y)

-- | Tests if a relation \( R \subseteq A \times A \) has the unique normal form
-- property with respect to reduction, i.e., \( \forall a,b \in A \) with
-- \( a \neq b \) holds: if \(a\) and \(b\) are normal forms, then
-- \( (a,b) \notin ((R^{*})^{-1} \circ R^{*}) \).
--
-- Formula size: linear in \( |A|^3 \)
uniqueNFsReduction :: Ix a => Relation a a -> Bit
uniqueNFsReduction r = and $ do
  let trc = transitiveReflexiveClosure r
  (x,y) <- indices r
  guard $ x < y
  return $ (isNF x r && isNF y r) ==> not $ peak trc trc ! (x,y)
