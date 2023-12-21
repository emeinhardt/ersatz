--------------------------------------------------------------------
-- |
-- Copyright :  © Edward Kmett 2010-2014, Johan Kiviniemi 2013
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
--------------------------------------------------------------------

{-# language OverloadedStrings #-}

module Ersatz.Solver.Minisat
  ( minisat
  , minisat'
  , cryptominisat
  , minisatPath
  , minisatPath'
  , minisatArg
  , cryptominisat5
  , cryptominisat5'
  , cryptominisat5Path
  , cryptominisat5Path'
  , cryptominisat5Arg
  , anyminisat
  ) where

import Control.Exception (IOException, handle)
import Control.Monad.IO.Class
import qualified Data.ByteString.Char8 as B
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap (IntMap)
import Data.List ( foldl' )
import Ersatz.Problem ( SAT, writeDimacs' )
import Ersatz.Solution
import Ersatz.Solver.Common
import System.Process (readProcessWithExitCode)

-- | Hybrid 'Solver' that tries to use: 'cryptominisat5', 'cryptominisat', and
-- 'minisat'.
anyminisat :: Solver SAT IO
anyminisat = trySolvers [cryptominisat5, cryptominisat, minisat]

-- | 'Solver' for 'SAT' problems that tries to invoke the @minisat@ executable
-- from the @PATH@.
minisat :: MonadIO m => Solver SAT m
minisat = minisatPath "minisat"

-- | 'Solver' for 'SAT' problems that tries to invoke the @minisat@ executable
-- from the @PATH@.
minisat' :: (MonadIO m, Show a) => [SolverArg a] -> Solver SAT m
minisat' = minisatPath' "minisat"


minisatPrefix, minisatSep :: Char
minisatPrefix = '-'
minisatSep = '='

minisatArg :: Show a => SolverArg a -> String
minisatArg (SolverFlag   f  ) = minisatPrefix:f
minisatArg (SolverOption o v) = minisatPrefix:o ++ minisatSep:show v


-- | 'Solver' for 'SAT' problems that tries to invoke the @cryptominisat@
-- executable from the @PATH@.
cryptominisat :: MonadIO m => Solver SAT m
cryptominisat = minisatPath "cryptominisat"


-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes
-- @minisat@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
minisatPath :: MonadIO m => FilePath -> Solver SAT m
minisatPath path = minisatPath' path ([] :: [SolverArg String])

-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes
-- @minisat@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
minisatPath' :: (MonadIO m, Show a) => FilePath -> [SolverArg a] -> Solver SAT m
minisatPath' path args problem = liftIO $
  withTempFiles ".cnf" "" $ \problemPath solutionPath -> do
    writeDimacs' problemPath problem

    (exit, _out, _err) <-
      readProcessWithExitCode path
                              (  (minisatArg <$> args)
                              ++ [problemPath, solutionPath])
                              []

    sol <- parseSolutionFile solutionPath

    return (resultOf exit, sol)


parseSolutionFile :: FilePath -> IO (IntMap Bool)
parseSolutionFile path = handle handler (parseSolution <$> B.readFile path)
  where
    handler :: IOException -> IO (IntMap Bool)
    handler _ = return IntMap.empty

parseSolution :: B.ByteString -> IntMap Bool
parseSolution s =
  case B.words s of
    x:ys | x == "SAT" ->
      foldl' ( \ m y ->
                 case B.readInt y of
                   Just (v,_) -> if   0 == v
                                 then m
                                 else IntMap.insert (abs v) (v>0) m
                   Nothing    -> error $
                                   "parseSolution: Expected an Int, received "
                                   ++ show y
             ) IntMap.empty ys
    _ -> IntMap.empty -- WRONG (should be Nothing)



-- | 'Solver' for 'SAT' problems that tries to invoke the @cryptominisat5@
-- executable from the @PATH@.
cryptominisat5 :: MonadIO m => Solver SAT m
cryptominisat5 = cryptominisat5Path "cryptominisat5"

-- | 'Solver' for 'SAT' problems that tries to invoke the @cryptominisat5@
-- executable from the @PATH@.
cryptominisat5' :: (MonadIO m, Show a) => [SolverArg a] -> Solver SAT m
cryptominisat5' = cryptominisat5Path' "cryptominisat5"


cryptominisat5Prefix :: String
cryptominisat5Prefix = "--"

cryptominisat5Sep :: Char
cryptominisat5Sep = ' '

cryptominisat5Arg :: Show a => SolverArg a -> String
cryptominisat5Arg (SolverFlag   f  ) =
  cryptominisat5Prefix ++ f
cryptominisat5Arg (SolverOption o v) =
  cryptominisat5Prefix ++ o ++ cryptominisat5Sep:show v

-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes
-- @cryptominisat5@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
cryptominisat5Path :: MonadIO m => FilePath -> Solver SAT m
cryptominisat5Path path = cryptominisat5Path' path ([] :: [SolverArg String])

-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes
-- @cryptominisat5@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
cryptominisat5Path' :: (MonadIO m, Show a)
  => FilePath
  -> [SolverArg a]
  -> Solver SAT m
cryptominisat5Path' path args problem = liftIO $
  withTempFiles ".cnf" "" $ \problemPath _ -> do
    writeDimacs' problemPath problem

    (exit, out, _err) <-
      readProcessWithExitCode path
                              ( (words . cryptominisat5Arg =<< args)
                              ++ [problemPath])
                              []

    let sol = parseSolution5 out

    return (resultOf exit, sol)
