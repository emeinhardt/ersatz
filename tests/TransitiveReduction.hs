{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ImportQualifiedPost #-}
-- | Tests a property @transitive_reduction_of@ that checks whether @tr@ is a
-- transitive reduction of a relation @r@.
--
-- Does this by testing that:
--
--  - The transitive reduction property is *sound*:
--    1. The transitive closure of @tr@ is the same as the transitive closure of
--       @r@.
--    2. There is no relation @r'@ with the same transitive closure as @r@ but
--       with strictly fewer edges than @tr@.
--  - The transitive reduction property is *complete*:
--    - If a relation @r'@ has the same transitive closure closure as @r@ and the
--      same number of edges as @tr@, then @r'@ also is classified as a
--      transitive reduction by the property.

-- Pending TODO summary:
--  - Simplify (and reduce dependency footprint) by moving poor man's benchmarking
--    code into a benchmark.
--  - There's probably other encodings of @transitive_reduction_of@ as a property
--    or as an operation and a benchmark suite would be useful to evaluate them.

module Main where

import Prelude hiding
  ( not
  , or
  , and
  , (&&)
  )
import Prelude qualified as P
import Data.Composition
  ( (.:)
  )
import Control.Arrow
  ( (***)
  , (&&&)
  )
import Data.Foldable qualified as F

import Control.Monad
  ( join
  , liftM2
  , foldM
  , msum
  )
import Control.Monad.State.Lazy
  ( StateT
  , MonadIO
  )

import Control.Monad.Trans.Maybe
  ( MaybeT (MaybeT)
  , runMaybeT
  )
import Control.Monad.Except
  ( ExceptT (ExceptT)
  , runExceptT
  , MonadError
  )
import Control.Monad.IO.Class
  ( liftIO
  )

import Data.Ix    qualified as Ix
import Data.Array qualified as A
import Data.Ix
  ( Ix
  )
import Data.Array
  ( Array
  )

import System.Timeout
  ( timeout
  )
import Data.Time
  ( getZonedTime
  )

import Data.Default
  ( Default
  )

import Ersatz.Problem
  ( HasSAT
  )
import Ersatz.Solution
  ( Solver
  , Result(Satisfied)
  )
import Ersatz.Solver
  ( solveWith
  , cryptominisat5
  )
import Ersatz.Codec
  ( Codec
  , Decoded
  )
import Ersatz.Bit qualified as B
import Ersatz.Bit
  ( Bit
  , not
  , (&&)
  , assert
  )
import Ersatz.Bits
  ( Bits
  , sumBit
  )
import Ersatz.Equatable
  ( Equatable ( (===)
              )
  )
import Ersatz.Orderable
  ( Orderable ( (<?)
              )
  )
import Ersatz.Counting
  ( exactly
  , atmost
  )
import Ersatz.Relation qualified as R
import Ersatz.Relation
  ( Relation
  , bounds
  , relation
  , table
  , reflexive
  , irreflexive
  , anti_symmetric
  , transitive
  , total
  , elems
  , transitive_closure
  , transitive_reduction_of
  , equals
  )



-- | Monadic 'foldl' with early return via 'Either'/'ExceptT'.
foldEM :: forall m t e a b. (Monad m, Foldable t)
  => (b -> a -> m (Either e b))
  -> b
  -> t a
  -> m (Either e b)
foldEM f =
  -- Example of the most common use for the blackbird combinator @.:@:
  -- Slapping a (very boring and straightforward) postprocessing function @g@ on
  -- the output of a function @f@ applied to two arguments:
  --
  --   @g (f a b) = g .: f@
  --
  -- All the pointful version does is add highly redundant noise, particularly
  -- here where the type signature of a fold is likely to be very familiar, and
  -- the type signatures for newtypes/their unwrappers similarly familiar.
  --
  -- Note also that while the expression below is a reasonable use of
  -- tacit style, it is technically further reducible to the more cryptic:
  --
  --  @runExceptT .:. foldM . (ExceptT .:)@
  --
  -- However, I'd hazard that most people partial to tacit style would hesitate
  -- to introduce an expression of the form @(f .)@ or @(. f)@ (or @(f .:)@,
  -- etc.).
  --
  -- Nevertheless, given the familiarity of the type signature of
  -- folds (and the name and type signature of 'foldEM'), this is probably
  -- about as good of a case as any where half of a composition
  -- (@(ExceptT .:)@) *might* be reasonable tacit style.
  runExceptT .: foldM (ExceptT .: f)


-- | Monadic 'unfoldr' defined without adding to the dependency footprint.
unfoldrM :: forall m a b. (Monad m)
  => (b -> m (Maybe (a, b)))
  -> b
  -> m [a]
unfoldrM f z =
  let go :: b -> m [a] -> m [a]
      go b mas = maybe mas
                       (\(a,b') ->
                          go b'
                          $ fmap (a:) mas)
                 =<< f b
  in go z $ pure []



-- | Find the first parameter value @a@ in a @ta :: t a@ that leads
-- to a monadic action @:: a -> m (Maybe b)@ succeeding and returns the
-- successful result.
--
-- An example with side-effects, demonstrating that this terminates early rather
-- than evaluating the full input first:
--
-- >>> as = [3,5,4,1,2,4,6,7] :: [Int]
-- >>> justWhenEven n = if even n then Just n else Nothing
-- >>> justWhenEvenM n = putStrLn "Launching the missiles!" >> pure (justWhenEven n)
-- >>> findFirstSuccess justWhenEvenM xs
-- Launching the missiles!
-- Launching the missiles!
-- Launching the missiles!
-- Just 4
findFirstSuccess :: forall m t a b. (Monad m, Functor t, Foldable t)
  => (a -> m (Maybe b))  -- ^ A parameterized effectful action that can fail.
  -> t a                 -- ^ A collection of parameters to try the action with.
  -> m (Maybe b)         -- ^ The first successful result (if any).
findFirstSuccess f =
  runMaybeT . msum . fmap (MaybeT . f)

-- | Variant on 'findFirstSuccess' that finds the first parameter value @a@ in
-- a @ta :: t a@ (if any) that leads to a short-circuiting ("Left", "error")
-- value and return that short-circuiting result.
--
-- An example with side-effects, demonstrating that this terminates early rather
-- than evaluating the full input first:
--
-- >>> as = [3,5,4,1,2,4,6,7] :: [Int]
-- >>> justWhenEven n = liftEither $ if even n then Left n else Right ()
-- >>> justWhenEvenM n = liftIO (putStrLn "Launching the missiles!") >> justWhenEven n
-- >>> runExceptT $ findFirstFailure justWhenEvenM () as
-- Launching the missiles!
-- Launching the missiles!
-- Launching the missiles!
-- Just 4
findFirstFailure :: forall m e t a b. (MonadError e m, Foldable t)
  => (a -> m b)  -- ^ A parameterized effectful action that can fail.
  -> b           -- ^ A value to return if the parameter collection is empty.
  -> t a         -- ^ A collection of parameters to try the action with.
  -> m b         -- ^ The first successful result (if any).
findFirstFailure = foldM . const

-- | Variant on 'findFirstSuccess' that collects all consecutive successes,
-- halting on the first failure. Successes are returned in reverse order, most
-- recent (last) first.
--
-- An example with side-effects, demonstrating that this terminates early rather
-- than evaluating the full input and then filtering it:
--
-- >>> as = [2,4,5,10,12,7] :: [Int]
-- >>> justWhenEven n = if even n then Just n else Nothing
-- >>> justWhenEvenM n = putStrLn "Launching the missiles!" >> pure (justWhenEven n)
-- >>> findAllUntilFailure justWhenEvenM as
-- Launching the missiles!
-- Launching the missiles!
-- Launching the missiles!
-- [4,2]
findAllUntilFailure :: forall m t a b. (Monad m, Foldable t)
  => (a -> m (Maybe b))  -- ^ A parameterized effectful action that can fail.
  -> t a                 -- ^ A collection of parameters to try the action with.
  -> m [b]               -- ^ The sequence of sucessful results (recent-first)
                         -- preceding the the first failure (if any).
findAllUntilFailure f = let
     h :: [a] -> m (Maybe (b, [a]))
     h []      = pure Nothing
     h (a:as_) = g as_ <$> f a
     g :: [a] -> Maybe b -> Maybe (b, [a])
     g = fmap . flip (,)
  in unfoldrM h . F.toList



newtype TimedOut = TimedOut { unTimedOut :: Int }
  deriving stock (Eq, Ord, Show)

solveWithTimeout :: forall s a. (HasSAT s, Default s, Codec a)
  => Int          -- ^ If positive, microseconds to wait before timing out.
                  -- If negative, waits indefinitely.
                  -- See note on sensitivity to platform-specific `maxBound @Int`
                  -- in 'System.Timeout'.
  -> Solver s IO
  -> StateT s IO a
  -> IO (Either TimedOut (Result, Maybe (Decoded a)))
solveWithTimeout n s q =
  let
     h Nothing  = Left $ TimedOut n
     h (Just r) = Right r
  in h <$> timeout n (solveWith s q)



preorder :: (Ix a) => Relation a a -> Bit
preorder = uncurry (&&) . (reflexive &&& transitive)

partial_order :: (Ix a) => Relation a a -> Bit
partial_order = uncurry (&&) . (preorder &&& anti_symmetric)

strict_partial_order :: (Ix a) => Relation a a -> Bit
strict_partial_order = uncurry (&&) . (irreflexive &&& transitive)

total_order :: (Ix a) => Relation a a -> Bit
total_order = uncurry (&&) . (partial_order &&& total)



sameTransitiveClosure :: (Ix a) => Relation a a -> Relation a a -> Bit
sameTransitiveClosure =
  uncurry equals . (transitive_closure *** transitive_closure) .: (,)

card :: (Ix a) => Relation a a -> Bits
card = sumBit . elems

fewerEdges :: (Ix a, Orderable a) => Relation a a -> Relation a a -> Bit
fewerEdges = uncurry (<?) . (card *** card) .: (,)

sameNumEdges :: (Ix a, Orderable a) => Relation a a -> Relation a a -> Bit
sameNumEdges = uncurry (===) . (card *** card) .: (,)



type B2 = (Bool, Bool)
type B3 = (Bool, Bool, Bool)

instance Enum B2 where
  toEnum 0 = (False, False)
  toEnum 1 = (False, True )
  toEnum 2 = (True , False)
  toEnum 3 = (True , True )

  fromEnum (False, False) = 0
  fromEnum (False, True ) = 1
  fromEnum (True , False) = 2
  fromEnum (True , True ) = 3

instance Enum B3 where
  toEnum 0 = (False, False, False)
  toEnum 1 = (False, False, True )
  toEnum 2 = (False, True , False)
  toEnum 3 = (False, True , True )
  toEnum 4 = (True , False, False)
  toEnum 5 = (True , False, True )
  toEnum 6 = (True , True , False)
  toEnum 7 = (True , True , True )

  fromEnum (False, False, False) = 0
  fromEnum (False, False, True ) = 1
  fromEnum (False, True , False) = 2
  fromEnum (False, True , True ) = 3
  fromEnum (True , False, False) = 4
  fromEnum (True , False, True ) = 5
  fromEnum (True , True , False) = 6
  fromEnum (True , True , True ) = 7


bar :: String
bar = replicate 40 '-'


-- Given the definition of @transitive_reduction_of@, this isn't that valueable of a test,
-- but it would be valuable for testing a function in @Ersatz.Relation.Op@
-- (@transitive_reduction_of@ is a @Prop@) that /constructs/ a symbolic relation that
-- must be a transitive reduction of some other relation.
data SameTcCx a = SameTcCx { rel    :: Array (a,a) Bool
                           , bad_tr :: Array (a,a) Bool
                           } deriving stock (Eq, Ord, Show)

trAlwaysHasSameTc :: (Ix a, Enum a, Equatable a)
  => ((a,a),(a,a))
  -> Maybe (String, Relation a a -> Bit)
  -> IO (Either (SameTcCx a) ())
trAlwaysHasSameTc dims p = do
  res <- solveWith cryptominisat5 $ do
    r  <- relation dims
    maybe (return ()) (\(_, p') -> assert $ p' r ) p

    tr <- relation (bounds r)
    assert $ transitive_reduction_of tr r

    assert $ not $ sameTransitiveClosure r tr

    return (r, transitive_closure r, tr, transitive_closure tr)
  case res of
    (Satisfied, Just (r, tc_r, tr, tc_tr)) -> do
       putStrLn "Putative transitive reduction of r does not always have the same transitive closure as r:"
       maybe (putStrLn "No global condition on r.")
             (putStrLn . ("Global condition on r: " ++) . fst)
             p
       putStrLn "r:"
       putStrLn $ table r
       putStrLn "Putative transitive reduction:"
       putStrLn $ table tr
       putStrLn "Transitive closure of r:"
       putStrLn $ table tc_r
       putStrLn "Transitive closure of putative transitive reduction:"
       putStrLn $ table tc_tr
       print =<< getZonedTime
       return $ Left $ SameTcCx r tr
    _ -> do
       putStrLn "Test passed: Transitive closure of transitive reduction of r is always == transitive closure of r."
       maybe (putStrLn "No global condition on r.")
             (putStrLn . ("Global condition on r: " ++) . fst)
             p
       print =<< getZonedTime
       return $ Right ()


data IsMinimalCx a = IsMinimalCx { rel'    :: Array (a,a) Bool
                                 , bad_tr' :: Array (a,a) Bool
                                 , cx      :: Array (a,a) Bool
                                 } deriving stock (Eq, Ord, Show)

trIsMinimal :: (Ix a, Enum a, Equatable a, Orderable a)
  => ((a,a),(a,a))
  -> Maybe (String, Relation a a -> Bit)
  -> IO (Either (IsMinimalCx a) ())
trIsMinimal dims p = do
  res <- solveWith cryptominisat5 $ do
    r  <- relation dims
    maybe (return ()) (\(_, p') -> assert $ p' r ) p

    tr <- relation (bounds r)
    -- assert $ transitive_reduction_of tr r

    cx <- relation (bounds r)
    assert $   fewerEdges            cx tr
            && sameTransitiveClosure cx  r
            -- && sameTransitiveClosure cx tr

    assert $ transitive_reduction_of tr  r

    return (r, tr, cx)
  case res of
    (Satisfied, Just (r, tr, cx)) -> do
       putStrLn "Putative transitive reduction of r is not always a least relation with the same transitive closure as r:"
       maybe (putStrLn "No global condition on r.")
             (putStrLn . ("Global condition on r: " ++) . fst)
             p
       putStrLn "r:"
       putStrLn $ table r
       putStrLn "Putative transitive reduction:"
       putStrLn $ table tr
       putStrLn "Relation with the same transitive closure as r but fewer edges than the putative transitive reduction:"
       putStrLn $ table cx
       print =<< getZonedTime
       return $ Left $ IsMinimalCx r tr cx
    _ -> do
      putStrLn "Test passed: There is never a relation smaller than a transitive reduction of r with the same transitive closure as r."
      maybe (putStrLn "No global condition on r.")
            (putStrLn . ("Global condition on r: " ++) . fst)
            p
      print =<< getZonedTime
      return $ Right ()


-- TODO the nested Eithers are a bit of a pain.
-- One out-of-scope solution would be to add TimedOut as a Result constructor —
-- or opening the door to a wider variety of richer error types?
-- If this were anything but a fairly narrow test suite, unifying @TimedOut@ with
-- the other error type (@IsMinimalCx@) is another salient option.
trIsMinimal' :: (Ix a, Enum a, Equatable a, Orderable a)
  => Int
  -> Int
  -> ((a,a),(a,a))
  -> Maybe (String, Relation a a -> Bit)
  -> IO (Either TimedOut (Either (IsMinimalCx a) ()))
trIsMinimal' n numEdges dims p = do
  res <- solveWithTimeout n cryptominisat5 $ do
    r  <- relation dims

    assert $ exactly numEdges $ elems r
    maybe (return ()) (\(_, p') -> assert $ p' r ) p

    tr <- relation (bounds r)
    -- assert $ transitive_reduction_of tr r
    assert $ atmost numEdges $ elems tr      -- does this help?

    cx <- relation (bounds r)
    assert $ atmost numEdges $ elems cx
    assert $   fewerEdges            cx tr
            && sameTransitiveClosure cx  r
            -- && sameTransitiveClosure cx tr

    assert $ transitive_reduction_of tr  r

    return (r, tr, cx)
  case res of
      (Left (TimedOut n)) -> do
         _ <- liftIO
            $ putStrLn
            $ unwords [ "Timed out (" ++ show n , "microseconds)"
                      , "attempting to show that for a relation r"
                      , "with", show numEdges , "edges"
                      , "there is a counterexample relation with the same"
                      , "transitive closure as r but which is smaller than"
                      , "a putative transitive reduction of r."
                      ]
         putStrLn $ unwords ["Cardinality condition: r must have exactly", show numEdges, "edges."]
         maybe (putStrLn "No global condition on r.")
               (putStrLn . ("Global condition on r: " ++) . fst)
               p
         print =<< getZonedTime
         putStrLn bar
         return $ Left $ TimedOut n
      (Right (Satisfied, Just (r, tr, cx))) -> do
         putStrLn "Putative transitive reduction of r is not always a least relation with the same transitive closure as r:"
         putStrLn $ unwords ["Cardinality condition: r must have exactly", show numEdges, "edges."]
         maybe (putStrLn "No global condition on r.")
               (putStrLn . ("Global condition on r: " ++) . fst)
               p
         putStrLn "r:"
         putStrLn $ table r
         putStrLn "Putative transitive reduction:"
         putStrLn $ table tr
         putStrLn "Relation with the same transitive closure as r but fewer edges than the putative transitive reduction:"
         putStrLn $ table cx

         print =<< getZonedTime
         putStrLn bar
         return $ Right . Left $ IsMinimalCx r tr cx
      _ -> do
        putStrLn "Test passed: There is never a relation smaller than a transitive reduction of r with the same transitive closure as r."
        putStrLn $ unwords ["Cardinality condition: r must have exactly", show numEdges, "edges."]
        maybe (putStrLn "No global condition on r.")
              (putStrLn . ("Global condition on r: " ++) . fst)
              p
        print =<< getZonedTime
        putStrLn bar
        return $ Right . Right $ ()


data IsCompleteCx a = IsCompleteCx { rel_    :: Array (a,a) Bool
                                   , bad_tr_ :: Array (a,a) Bool
                                   , cx_     :: Array (a,a) Bool
                                   } deriving stock (Eq, Ord, Show)

trIsComplete :: (Ix a, Enum a, Equatable a, Orderable a)
  => ((a,a),(a,a))
  -> Maybe (String, Relation a a -> Bit)
  -> IO (Either (IsCompleteCx a) ())
trIsComplete dims p = do
  res <- solveWith cryptominisat5 $ do
    r  <- relation dims
    maybe (return ()) (\(_, p') -> assert $ p' r ) p

    tr <- relation (bounds r)
    -- assert $ transitive_reduction_of tr r

    cx <- relation (bounds r)
    assert $   sameNumEdges          cx tr
            && sameTransitiveClosure cx  r
            -- && sameTransitiveClosure cx tr

    assert $       transitive_reduction_of tr  r
    assert $ not $ transitive_reduction_of cx  r

    return (r, tr, cx)
  case res of
    (Satisfied, Just (r, tr, cx)) -> do
       putStrLn "A relation with the same number of edges as a transitive reduction of r and the same transitive closure is not classified as a transitive reduction:"
       maybe (putStrLn "No global condition on r.")
             (putStrLn . ("Global condition on r: " ++) . fst)
             p
       putStrLn "r:"
       putStrLn $ table r
       putStrLn "Transitive reduction:"
       putStrLn $ table tr
       putStrLn "Relation with the same transitive closure as r + the same number of edges as the transitive reduction, but which isn't considered a transitive reduction:"
       putStrLn $ table cx
       print =<< getZonedTime
       return $ Left $ IsCompleteCx r tr cx
    _ -> do
      putStrLn "Test passed: There is never a relation with the same transitive closure as r and the same number of edges as a transitive reduction, but which is not considered a transitive reduction."
      maybe (putStrLn "No global condition on r.")
            (putStrLn . ("Global condition on r: " ++) . fst)
            p
      print =<< getZonedTime
      return $ Right ()



newtype Microsec = Microsec { unMicrosec :: Int }
    deriving stock (Eq, Ord, Show)

secToMicrosec :: Int -> Microsec
secToMicrosec = Microsec . (round (10 ^^ 6) *)

minToMicrosec :: Int -> Microsec
minToMicrosec = secToMicrosec . (60 *)

main :: IO ()
main = let
     mkDims :: forall x. (Bounded x) => ((x,x), (x,x))
     mkDims = ((minBound, minBound), (maxBound, maxBound))

     maxEdges :: Int -> Integer
     maxEdges n
       | n < 0 = 0
       | otherwise = round $ 2 ^^ (n * n)
  in do
    putStrLn "Completeness tests: If tr is a transitive reduction of r, then every relation tr' with the same number of edges and transitive closure as tr is also classified a transitive reduction."
    putStrLn "2 bits:"
    _ <- trAlwaysHasSameTc (mkDims @B2) (Just ("strict partial order", strict_partial_order))
    putStrLn bar
    _ <- trAlwaysHasSameTc (mkDims @B2) (Just ("partial order", partial_order))
    putStrLn bar
    _ <- trAlwaysHasSameTc (mkDims @B2) (Just ("preorder", preorder))
    putStrLn bar
    _ <- trAlwaysHasSameTc (mkDims @B2) Nothing
    putStrLn bar

    putStrLn "3 bits:"
    _ <- trAlwaysHasSameTc (mkDims @B3) (Just ("strict partial order", strict_partial_order))
    putStrLn bar
    _ <- trAlwaysHasSameTc (mkDims @B3) (Just ("partial order", partial_order))
    putStrLn bar
    -- Tests above should take seconds; test below should take about 30s.
    _ <- trAlwaysHasSameTc (mkDims @B3) (Just ("preorder", preorder))
    putStrLn bar
    -- Test below should take roughly a minute.
    _ <- trAlwaysHasSameTc (mkDims @B3) Nothing
    putStrLn bar

    putStrLn ""

    putStrLn "Soundness tests: transitive closure of a transitive reduction of r ≡ the transitive closure of r."
    putStrLn "2 bits:"
    _ <- trAlwaysHasSameTc (mkDims @B2) (Just ("strict partial order", strict_partial_order))
    putStrLn bar
    _ <- trAlwaysHasSameTc (mkDims @B2) (Just ("partial order", partial_order))
    putStrLn bar
    _ <- trAlwaysHasSameTc (mkDims @B2) (Just ("preorder", preorder))
    putStrLn bar
    _ <- trAlwaysHasSameTc (mkDims @B2) Nothing
    putStrLn bar

    putStrLn "3 bits:"
    _ <- trAlwaysHasSameTc (mkDims @B3) (Just ("strict partial order", strict_partial_order))
    putStrLn bar
    _ <- trAlwaysHasSameTc (mkDims @B3) (Just ("partial order", partial_order))
    putStrLn bar
    -- Tests above should take seconds; next two will take 1-2 min.
    _ <- trAlwaysHasSameTc (mkDims @B3) (Just ("preorder", preorder))
    putStrLn bar
    _ <- trAlwaysHasSameTc (mkDims @B3) Nothing
    putStrLn bar

    putStrLn ""

    putStrLn "Soundness tests: A transitive reduction of r is minimal."
    -- This block of tests should take seconds.
    putStrLn "2 bits:"
    _ <- trIsMinimal (mkDims @B2) (Just ("strict partial order", strict_partial_order))
    putStrLn bar
    _ <- trIsMinimal (mkDims @B2) (Just ("partial order", partial_order))
    putStrLn bar
    _ <- trIsMinimal (mkDims @B2) (Just ("preorder", preorder))
    putStrLn bar
    _ <- trIsMinimal (mkDims @B2) Nothing
    putStrLn bar

    -- Next two tests should take seconds.
    putStrLn "3 bits:"
    _ <- trIsMinimal (mkDims @B3) (Just ("strict partial order", strict_partial_order))
    putStrLn bar
    _ <- trIsMinimal (mkDims @B3) (Just ("partial order", partial_order))
    putStrLn bar
    -- Only takes about 2 min to get to this point, but the next test takes
    -- an infeasible amount of time to run.
    -- _ <- trIsMinimal (mkDims @B3) (Just ("preorder", preorder))
    -- putStrLn bar
    -- _ <- trIsMinimal (mkDims @B3) Nothing
    -- putStrLn bar

    -- Hazily moving from tests into benchmarking, we'll change the search
    -- to look upwards through the space of the number of edges in the
    -- starting relation (see 'trIsMinimal'/ 'trIsMinimal\'') until it
    -- takes more than 10-15 minutes to find an answer and see how fast
    -- progress starts to slow; this also provides a more granular window
    -- into whether any upstream changes are useful.
    -- TODO write a proper benchmark suite.
    -- let numEdges'           = [29..maxEdges . fromEnum $ maxBound @B3]
    let numEdges'             = [0..maxEdges . fromEnum $ maxBound @B3]
        maxInt                = (fromIntegral @Int @Integer) (maxBound @Int)
        numEdges              = map (fromIntegral @Integer @Int)
                              . filter (<= maxInt)
                              $ numEdges'
        oneMin                = minToMicrosec 1
        threeMin              = minToMicrosec 3
        fiveMin               = minToMicrosec 5
        tenMin                = minToMicrosec 10
        fifteenMin            = minToMicrosec 15
        eitherToMaybe         = either (const Nothing) Just
        trIsMinimalPro nEdges = trIsMinimal' (unMicrosec fifteenMin)
                                             nEdges
                                             (mkDims @B3)
                                             (Just ("preorder", preorder))
        trIsMinimal_   nEdges = trIsMinimal' (unMicrosec fifteenMin)
                                             nEdges
                                             (mkDims @B3)
                                             Nothing
    -- Relations with >= 52 edges are all apparently trivial to solve; takes about 1.5 hours to get to that point with > a ten minute timeout threshold.
    _ <- findAllUntilFailure (fmap eitherToMaybe . trIsMinimalPro) (filter (< 52) numEdges)

    -- with a 10 minute timeout, takes 20m to fail on 7 edges
    -- with a 15 minute timeout, takes 35 min to fail on 8 edges ;(
    _ <- findAllUntilFailure (fmap eitherToMaybe . trIsMinimal_  ) numEdges

    return ()
