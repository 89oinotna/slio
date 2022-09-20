{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil

import Data.List ((\\))
import SimpleStLIO (newLIORef, writeLIORef, readLIORef, unlabel)

data User = Data | App
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
                     , scurr = Rel [(Data,App)]
                     }

disallowDA :: SLIO User Rel ()
disallowDA = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel [])

directRelease :: SLIO User Rel String
directRelease = do
    dat <- label Data "data"
    disallowDA
    udat <- unlabel dat
    o <- newLIORef App udat
    readLIORef o


main :: IO ()
main = do
    (r, s) <- unSLIO directRelease initState
    print r
    print s