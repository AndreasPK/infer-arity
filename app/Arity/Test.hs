{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Test where

import Data.Map as M

data K = A | B | C

data Value k where
    Var :: Value k -- Always A or B
    ConstA :: Value A
    ConstB :: Value B
    ConstC :: Value C

type Env k = Map String (Value k)

lookupA :: Env A -> String -> Maybe (Value A)
lookupA mmap key = M.lookup key mmap