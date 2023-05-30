{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil

import Data.List ((\\))
import SimpleStLIO (unlabel)
import Control.Monad (forever)

data User = Book | Alice
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

allowBA :: SLIO User Rel ()
allowBA = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st ++ [(Book, Alice)])

disallowBA :: SLIO User Rel ()
disallowBA = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st \\[(Book, Alice)])

takeNotes :: Labeled User String -> SLIO User Rel (Labeled User String)
takeNotes input= do 
    i <- unlabel input
    label Alice $ "takeNotesd " ++ i
--     relabel input Alice


dr = do
    book <- label Book "libro"
    allowBA
    notes <- takeNotes book
    n <- unlabel notes
    disallowBA
    b <- relabel book Alice
    --book <- unlabel b
    unlabel notes
    --return b

main :: IO ()
main = do
    (r, s) <- unSLIO dr initState
    print r
    print s