{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil

import Data.List ((\\))
import SimpleStLIO (unlabel)

data User = Merch | Top | Card
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
                     , scurr = Rel [(Card, Merch)]
                     }

disallowCM :: SLIO User Rel ()
disallowCM = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st \\ [(Card, Merch)])

erasure :: SLIO User Rel String
erasure = do
    card <- label Card "code"
    -- uc <- unlabel credit_card
    -- copy <- newLIORef Merch uc
    copy <- relabel card Merch
    disallowCM
    unlabel copy

main :: IO ()
main = do
    (r, s) <- unSLIO erasure initState
    print r
    print s