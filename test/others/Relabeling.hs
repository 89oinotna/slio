{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil

import Data.List ((\\))

data User = Secret | Top | Pub
  deriving (Eq, Show)

newtype Rel = Rel [(User,User)] deriving (Show)

instance Label User Rel where
  lrt (Rel st) lbl1 lbl2  =  traceShow (show s) (lbl1,lbl2) `elem` reflTransClosure st
    where
        s = reflTransClosure st
  -- Check if there is any user who may see information
  -- from this user, and could not do before. If yes,
  -- the upper set is increased.
  incUpperSet (Rel oldSt) (Rel newSt) user =
    let others = [u | (_,u) <- newSt]
    in any (\u -> not (lrt (Rel oldSt) user u) &&
                      lrt (Rel newSt) user u
           ) others

initState :: LIOState User Rel
initState = LIOState { lcurr = []
                     , scurr = Rel []
                     }

allowTS = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st ++ [(Top, Secret)])

allowSP= do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st ++ [(Secret, Pub)])


disallowTS :: SLIO User Rel ()
disallowTS = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st \\ [(Top, Secret)])

relabeling :: SLIO User Rel String
relabeling = do
    top <- label Top "topsecert"
    allowTS
    sec <- relabel top Secret
    disallowTS
    allowSP
    pub <- relabel sec Pub
    unlabel pub

main :: IO ()
main = do
    (r, s) <- unSLIO relabeling initState
    print r
    print s