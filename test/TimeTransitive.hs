{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil

import Data.List ((\\))
import SimpleStLIO (unlabel, newLIORef)
import Debug.Trace (traceShowM)

data User = Input | Sanitizer | DB
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
    in traceShow others $ any (\u -> not (lrt (Rel oldSt) user u) &&
                      lrt (Rel newSt) user u
           ) others

initState :: LIOState User Rel
initState = LIOState { lcurr = []
                     , scurr = Rel [(Input, Sanitizer)]
                     }

disallowIS :: SLIO User Rel ()
disallowIS = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel [])

allowSD :: SLIO User Rel ()
allowSD = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st ++ [(Sanitizer, DB)])

escape :: Labeled User String -> SLIO User Rel (Labeled User String)
escape input= toLabeled Sanitizer $ do 
    i <- unlabel input
    return $ "escaped " ++ i

--timetransitive :: SLIO User Rel String
--timetransitive = do
--    input <- label Input "malicious code"
--    x <- escape input
--    xx <- unlabel x
--    disallowIS
--    traceShow "allowing" allowSD
--    db <- label DB xx
--    xx <- unlabel x
--    unlabel db

timetransitive2 :: SLIO User Rel String
timetransitive2 = do
    input <- label Input "malicious code"
    x <- escape input
    disallowIS
    traceShow x allowSD
--    xx <- unlabel x
    db <- relabel x DB
--    xx <- unlabel x
    unlabel db

main :: IO ()
main = do
    (r, s) <- unSLIO timetransitive2 initState
    print r
    print s