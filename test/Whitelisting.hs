{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil

import Data.List ((\\))
import SimpleStLIO (newLIORef, writeLIORef, readLIORef, unlabel)
import Data.Bits (Bits(xor))

data User = Secret | Pub | Key
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
                     , scurr = Rel [(Secret,Pub), (Key, Pub)]
                     }

disallowSP :: SLIO User Rel ()
disallowSP = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st \\ [(Secret, Pub)])

whitelisting :: SLIO User Rel String
whitelisting = do
    secret <- label Secret "secret"
    k <- label Key "key"
    secret <- unlabel secret
    k <- unlabel k
    pub <- newLIORef Pub (k ++ secret)
    disallowSP
    writeLIORef pub k
    traceShow "disallowing" $readLIORef pub


main :: IO ()
main = do
    (r, s) <- unSLIO whitelisting initState
    print r
    print s