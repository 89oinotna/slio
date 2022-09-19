{-# LANGUAGE MultiParamTypeClasses #-}
module NonDisclosurePol
  ( User(..)
  , Level(..)
  , NDState
  , NDLIO
  , flow
  , runNDLIO
  ) where

import SimpleStLIO
import SimpleStLIOUtil

import qualified Data.Set as S
import Data.List (nub, intersect)

data User = User String
  deriving (Eq, Ord, Show)

data Level = Level [User] | Bottom
  deriving (Eq, Ord, Show)

{----------------------------------------}
{-           LIO structure              -}
{----------------------------------------}

data NDState = NDState [(User, User)]

type NDLIO = SLIO Level NDState

instance Label Level NDState  where
  lrt _ Bottom _      = True
  lrt _ _      Bottom = False
  lrt (NDState st) (Level l1) (Level l2) = 
    all (\u2 -> any (\u1 -> (u1,u2) `elem` tSt) l1) l2
    where tSt = reflTransClosure st
  -- Check if there is any new user who may see information from any user
  -- in the provided label. If so, the upper set is increased.
  incUpperSet oldSt newSt@(NDState st) (Level lbl) =
    let others = [u | (_,u) <- st]
    in any (\lu -> any (\u -> not (lrt oldSt (Level [lu]) (Level [u])) && (lrt newSt (Level [lu]) (Level [u]))) others) lbl

flow :: (User, User) -> NDLIO a -> NDLIO a
flow (from, to) comp = do 
  (NDState st) <- getState
  setState (NDState $ (from,to):st)
  a <- comp
  setState (NDState st)
  return a

runNDLIO :: NDLIO a -> IO (a, LIOState Level NDState)
runNDLIO comp = 
  unSLIO comp (LIOState { lcurr = []
                        , scurr = NDState []   } )
