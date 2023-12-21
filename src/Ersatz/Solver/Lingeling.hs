{-# LANGUAGE OverloadedStrings #-}

module Ersatz.Solver.Lingeling
  ( lingeling
  , lingeling'
  , lingelingPath
  , lingelingPath'
  , lingelingArg

  , plingeling
  , plingeling'
  , plingelingPath
  , plingelingPath'
  , plingelingArg

  , treengeling
  , treengeling'
  , treengelingPath
  , treengelingPath'
  , treengelingArg
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

-- | 'Solver' for 'SAT' problems that tries to invoke the @lingeling@ executable
-- from the @PATH@.
lingeling :: MonadIO m => Solver SAT m
lingeling = lingelingPath "lingeling"

-- | 'Solver' for 'SAT' problems that tries to invoke the @plingeling@ executable
-- from the @PATH@.
plingeling :: MonadIO m => Solver SAT m
plingeling = plingelingPath "plingeling"

-- | 'Solver' for 'SAT' problems that tries to invoke the @treengeling@ executable
-- from the @PATH@.
treengeling :: MonadIO m => Solver SAT m
treengeling = treengelingPath "treengeling"

-- | 'Solver' for 'SAT' problems that tries to invoke the @lingeling@ executable
-- from the @PATH@.
lingeling' :: (MonadIO m, Show a) => [SolverArg a] -> Solver SAT m
lingeling' = lingelingPath' "lingeling"

-- | 'Solver' for 'SAT' problems that tries to invoke the @plingeling@ executable
-- from the @PATH@.
plingeling' :: (MonadIO m, Show a) => [SolverArg a] -> Solver SAT m
plingeling' = plingelingPath' "plingeling"

-- | 'Solver' for 'SAT' problems that tries to invoke the @treengeling@ executable
-- from the @PATH@.
treengeling' :: (MonadIO m, Show a) => [SolverArg a] -> Solver SAT m
treengeling' = treengelingPath' "treengeling"


shortOpt :: Char
shortOpt = '-'

longOpt :: String
longOpt = "--"

wsSep :: Char
wsSep = ' '

eqSep :: Char
eqSep = '='

-- Flags based on lingeling version "bcp"
lingelingShortFlags, lingelingShortOpts :: [String]
lingelingShortFlags = [ "q"
                      , "s"
                      , "h"
                      , "f"
                      , "r"
                      , "d"
                      , "P"
                      , "e"
                      , "n"
                      , "c"
                      , "l"
                      , "v"
                      ]
lingelingShortOpts = [ "o"
                     , "p"
                     , "T"
                     , "a"
                     ]

lingelingArg :: Show a => SolverArg a -> String
lingelingArg (SolverOption "O" level) =
  shortOpt:"O" ++ show level
lingelingArg s                        =
  ngelingArg lingelingShortFlags lingelingShortOpts s

-- Flags based on plingeling version "bcp"
plingelingShortFlags, plingelingShortOpts :: [String]
plingelingShortFlags = [ "h"
                       , "v"
                       , "n"
                       , "p"
                       ]
plingelingShortOpts = [ "t"
                      , "m"
                      , "g"
                      , "l"
                      ]

plingelingArg :: Show a => SolverArg a -> String
plingelingArg = ngelingArg plingelingShortFlags plingelingShortOpts

-- Flags based on treengeling version "bcp"
treengelingShortFlags, treengelingShortOpts :: [String]
treengelingShortFlags = [ "h"
                        , "v"
                        , "s"
                        , "n"
                        ]
treengelingShortOpts = [ "t"
                       , "a"
                       , "m"
                       , "g"
                       , "r"
                       , "s"
                       , "b"
                       , "f"
                       ]

treengelingArg :: Show a => SolverArg a -> String
treengelingArg = ngelingArg treengelingShortFlags treengelingShortOpts


ngelingArg :: Show a => [String] -> [String] -> SolverArg a -> String
ngelingArg shortFlags _         (SolverFlag   f  )
  | f `elem` shortFlags = shortOpt:f
  | otherwise           = longOpt ++ f
ngelingArg _          shortOpts (SolverOption o v)
  | o `elem` shortOpts = shortOpt:o   ++ wsSep:show v
  | otherwise          = longOpt ++ o ++ eqSep:show v


-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes
-- @lingeling@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
lingelingPath :: MonadIO m => FilePath -> Solver SAT m
lingelingPath = ngelingPath

-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes
-- @plingeling@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
plingelingPath :: MonadIO m => FilePath -> Solver SAT m
plingelingPath = ngelingPath

-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes
-- @treengeling@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
treengelingPath :: MonadIO m => FilePath -> Solver SAT m
treengelingPath = ngelingPath

-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes
-- @*ngeling@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
ngelingPath :: (MonadIO m)
  => FilePath
  -> Solver SAT m
ngelingPath path =
  ngelingPath' (ngelingArg [] []) path ([] :: [SolverArg String])


-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes
-- @lingeling@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
lingelingPath' :: (MonadIO m, Show a)
  => FilePath
  -> [SolverArg a]
  -> Solver SAT m
lingelingPath' = ngelingPath' lingelingArg

-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes
-- @plingeling@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
plingelingPath' :: (MonadIO m, Show a)
  => FilePath
  -> [SolverArg a]
  -> Solver SAT m
plingelingPath' = ngelingPath' plingelingArg

-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes
-- @treengeling@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
treengelingPath' :: (MonadIO m, Show a)
  => FilePath
  -> [SolverArg a]
  -> Solver SAT m
treengelingPath' = ngelingPath' treengelingArg


-- | 'Solver' for 'SAT' problems that tries to invoke a program that takes
-- @*ngeling@ compatible arguments.
--
-- The 'FilePath' refers to the path to the executable.
ngelingPath' :: (MonadIO m, Show a)
  => (SolverArg a -> String)
  -> FilePath
  -> [SolverArg a]
  -> Solver SAT m
ngelingPath' argToString path args problem = liftIO $
  withTempFiles ".cnf" "" $ \problemPath _ -> do
    writeDimacs' problemPath problem

    (exit, out, _err) <-
      readProcessWithExitCode path
                              ( (words . argToString =<< args)
                              ++ [problemPath])
                              []

    let sol = parseSolution5 out

    return (resultOf exit, sol)
