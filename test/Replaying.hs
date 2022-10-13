{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil
import Data.List ((\\))
import Data.Map (Map, lookup, insert, empty)
data User = NSA | Military
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
                     , scurr = Rel [(NSA, Military)]
                     , ntlab = []
                     , rlab = Data.Map.empty
                     }

disallowNM :: SLIO User Rel ()
disallowNM = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st \\ [(NSA, Military)])

unlabelAsReplaying :: Label l st => Labeled l a -> l -> SLIO l st a
unlabelAsReplaying ldata nl=do 
  d <- relabel ldata nl
  unlabel d

replaying :: SLIO User Rel String
replaying = do
    file <- label (Military) "secret"
    file1 <- unlabelAsReplaying file (Military)
    mil <- newLIORef (Military) file1
    writeLIORef mil ""
    disallowNM
    writeLIORef mil file1
    readLIORef mil


main :: IO ()
main = do
    (r, s) <- unSLIO replaying initState
    print r
    print s