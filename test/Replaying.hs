{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil

import Data.List ((\\), nub)
import SimpleStLIO (newLIORef, writeLIORef, readLIORef, LIOState)
import Data.Map (Map, lookup, insert, empty)

newtype User = User String
  deriving (Eq, Show)

newtype Rel = Rel [(User, User)] deriving (Show)



instance Label User Rel where
  -- lcurr must be added to have refl of labels not in st
  lrt (Rel st) lcurr lbl1 lbl2  =  traceShow (s) (lbl1,lbl2) `elem` s
    where
        r = refl lcurr
        s = reflTransClosure $ nub (st++r)
  -- Check if there is any user who may see information
  -- from this user, and could not do before. If yes,
  -- the upper set is increased.
  incUpperSet (Rel oldSt) (Rel newSt) lcurr user =
    let others = [u | (_,u) <- newSt]
    in any (\u -> not (lrt (Rel oldSt) lcurr user u) &&
                      lrt (Rel newSt) lcurr user u
           ) others

initState :: LIOState User Rel
initState = LIOState { lcurr = []
                     , scurr = Rel [(User "NSA", User "Military"), (User "NSA", User "Another")]
                     , ntlab = []
                     , rlab = Data.Map.empty
                     }

disallowNM :: SLIO User Rel ()
disallowNM = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st \\ [])



replaying :: SLIO User Rel String
replaying = do
    file <- label (User "NSA") "secret"
    --file <- unlabelAsReplaying file (User "Military")
    file <- unlabel file
    mil <- newLIORef (User "Military") file
    writeLIORef mil ""
    disallowNM
    writeLIORef mil file
    readLIORef mil

-- ______________________

unlabelAsReplaying :: Label l st => Labeled l a -> l -> SLIO l st a
unlabelAsReplaying ldata nl=do 
  d <- relabel ldata nl
  unlabel d 

replaying2 :: SLIO User Rel String
replaying2 = do
    file <- label (User "NSA") "secret"
    file <- unlabelAsReplaying file (User "Military") --wrong
    --file <- unlabel file
    mil <- newLIORef (User "Military") file
    an <- newLIORef (User "Another") file
    writeLIORef mil ""
    --disallowNM
    writeLIORef mil file
    readLIORef mil
-- ______________________

main :: IO ()
main = do
    (r, s) <- unSLIO replaying initState
    print r
    print s