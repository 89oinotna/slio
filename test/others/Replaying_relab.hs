{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil
import Data.List ((\\))

newtype User = User String
  deriving (Eq, Show)

newtype Rel = Rel [(User, User)] deriving (Show)



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
                     , scurr = Rel [(User "NSA", User "ReplTmp"), (User "ReplTmp", User "NSA"), (User "NSA", User "Military"), (User "ReplTmp", User "Military")]
                     , tlab = []
                     }

disallowNM :: SLIO User Rel ()
disallowNM = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st \\ [(User "NSA", User "Military")])


disallowNR :: SLIO User Rel ()
disallowNR = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st \\ [(User "NSA", User "ReplTmp")])

replaying :: SLIO User Rel String 
replaying = do
    file <- label (User "NSA") "secret"
    file <- relabel file (User "ReplTmp")
    file <- unlabel file
    disallowNR
    mil <-  newLIORef (User "Military") file
    writeLIORef mil ""
    disallowNM
    writeLIORef mil file
    readLIORef mil


main :: IO ()
main = do
    (r, s) <- unSLIO replaying initState
    print r
    print s

-- replaying by relabeling is not ok