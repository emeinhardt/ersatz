{-# LANGUAGE OverloadedStrings #-}

module Ersatz.Solver.Kissat
  ( kissat
  , kissat'
  , kissatPath
  , kissatPath'
  , kissatArg
  ) where

import Control.Monad.IO.Class
  ( MonadIO ( liftIO
            )
  )
import Ersatz.Problem
  ( SAT
  , writeDimacs'
  )
import Ersatz.Solution
  ( Solver
  )
import Ersatz.Solver.Common
  ( SolverArg ( SolverFlag
              , SolverOption
              )
  , resultOf
  , withTempFiles
  , parseSolution5
  )
import System.Process
  ( readProcessWithExitCode
  )


-- | 'Solver' for 'SAT' problems that tries to invoke the @kissat@ executable
-- from the @PATH@.
kissat :: MonadIO m => Solver SAT m
kissat = kissatPath "kissat"

-- | 'Solver' for 'SAT' problems that tries to invoke the @kissat@ executable
-- from the @PATH@.
kissat' :: (MonadIO m, Show a) => [SolverArg a] -> Solver SAT m
kissat' = kissatPath' "kissat"


-- based on kissat 3.10
kissatShortFlags :: [String]
kissatShortFlags = [ "h"
                   , "f"
                   , "n"
                   , "q"
                   , "s"
                   , "v"
                   ]

kissatPrefix :: String
kissatPrefix = "--"

kissatSep :: Char
kissatSep = ' '

kissatArg :: Show a => SolverArg a -> String
kissatArg (SolverFlag   f  )
  | f `elem` kissatShortFlags = '-':f
  | otherwise                 = kissatPrefix ++ f
kissatArg (SolverOption o v)  = kissatPrefix ++ o ++ kissatSep:show v


-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes
-- @kissat@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
kissatPath :: MonadIO m => FilePath -> Solver SAT m
kissatPath path = kissatPath' path ([] :: [SolverArg String])

-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes
-- @kissat@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
kissatPath' :: (MonadIO m, Show a) => FilePath -> [SolverArg a] -> Solver SAT m
kissatPath' path args problem = liftIO $
  withTempFiles ".cnf" "" $ \problemPath _ -> do
    writeDimacs' problemPath problem

    (exit, out, _err) <-
      readProcessWithExitCode path
                              ( (kissatArg <$> args)
                              ++ [problemPath])
                              []

    let sol = parseSolution5 out

    return (resultOf exit, sol)
