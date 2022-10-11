{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil

newtype User = User String
  deriving (Eq, Show)

--newtype Flow l = Flow {getFlow ::(l,l)} deriving Show

type Flow l = (l,l)

newtype Rel = Rel [Flow User] deriving (Show)

instance Diff Rel where
    difference st1 st2= st1 \\ st2 

instance FlowTo ((,) User) User where
    source = fst 
    target = snd 

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

initState :: LIOState User Rel ((,) User)
initState = LIOState { lcurr = []
                     , scurr = Rel [(User "NSA", User "Military")]
                     , ntlab = []
                     , rlab =[]
                     }

disallowNM :: SLIO User Rel ((,) User)()
disallowNM = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel [])



replaying :: SLIO User Rel ((,) User) String
replaying = do
    file <- label (User "NSA") "secret"
    --file1 <- unlabel file
    mf <- label (User "Military") "boh"
    mf1 <- unlabel mf
    return mf1
    --unlabel $ sfmap (mf1 ++) file
    --mil <- newLIORef (User "Military") file
    -- writeLIORef mil ""
    -- disallowNM
    -- writeLIORef mil file
    -- readLIORef mil


main :: IO ()
main = do
    (r, s) <- unSLIO replaying initState
    print r
    print s