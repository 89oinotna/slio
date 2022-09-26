{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil

import Data.List ((\\))
import SimpleStLIO (unlabel)
import Control.Monad (forever)

data User = Alice | Film
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
                     , scurr = Rel [(Film, Alice)]
                     }

--leak :: SLIO User Rel String
leak = do
    film <- label Film "rev"
    film <- unlabel film
    o <- newLIORef Alice film
    disallow
    writeLIORef o "c"


disallow :: SLIO User Rel ()
disallow = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel [])

main :: IO ()
main = do
    (r, s) <- unSLIO leak initState
    print r
    print s