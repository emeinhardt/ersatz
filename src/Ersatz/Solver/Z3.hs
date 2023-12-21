--------------------------------------------------------------------
-- |
-- Copyright :  © Edward Kmett 2010-2014, Johan Kiviniemi 2013
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
--------------------------------------------------------------------
module Ersatz.Solver.Z3
  ( z3
  , z3Path
  , z3'
  , z3Path'
  , z3Arg
  ) where

import Control.Monad.IO.Class
import Ersatz.Problem ( SAT, writeDimacs' )
import Ersatz.Solution
import Ersatz.Solver.Common
import System.Process (readProcessWithExitCode)

-- | 'Solver' for 'SAT' problems that tries to invoke the @z3@ executable from
-- the @PATH@.
z3 :: MonadIO m => Solver SAT m
z3 = z3Path "z3"

-- | 'Solver' for 'SAT' problems that tries to invoke the @z3@ executable from
-- the @PATH@ and passes the specified solver arguments.
z3' :: (MonadIO m, Show a) => [SolverArg a] -> Solver SAT m
z3' = z3Path' "z3"


z3Prefix, z3OptSep, z3ParamSep :: Char
z3Prefix = '-'
z3OptSep = ':'
z3ParamSep = '='

-- Based on 4.8.17
z3Opts :: [String]
z3Opts = [ "v"
         , "pm"
         , "pp"
         , "tactics"
         , "T"
         , "t"
         ]

-- | Translates a 'SolverArg' to a single string.
z3Arg :: Show a => SolverArg a -> String
z3Arg (SolverFlag   f  ) = z3Prefix:f
z3Arg (SolverOption o v)
  | o `elem` z3Opts = z3Prefix:o ++ z3OptSep:show v
  | otherwise       = z3Prefix:o ++ z3ParamSep:show v


-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes @z3@
-- compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
z3Path :: MonadIO m => FilePath -> Solver SAT m
z3Path path = z3Path' path ([] :: [SolverArg String])

-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes @z3@
-- compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
z3Path' :: (MonadIO m, Show a) => FilePath -> [SolverArg a] -> Solver SAT m
z3Path' path args problem = liftIO $
  withTempFiles ".cnf" "" $ \problemPath _ -> do
    writeDimacs' problemPath problem

    (_exit, out, _err) <-
      readProcessWithExitCode path
                              (   (z3Arg <$> args)
                               ++ ["-dimacs", problemPath])
                              []

    let result = case lines out of
                    "s SATISFIABLE":_   -> Satisfied
                    "s UNSATISFIABLE":_ -> Unsatisfied
                    _                   -> Unsolved

    return (result, parseSolution5 out)
