{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil

import qualified Data.HashMap.Strict           as HM
import Data.List ((\\))
import SimpleStLIO (unlabel, newLIORef, getLabel)
import Debug.Trace (traceShow)
import  Impl

initState :: LIOState User Rel Rep
initState = LIOState { lcurr = HM.empty
                     , scurr = Rel [(User "Input", User "Sanitizer")]
                     , ntlab = HM.empty
                     , assocnt = HM.empty
  , rlab  = Rep HM.empty
  , newid = 0
  }

disallowIS :: SLIO User Rel Rep ()
disallowIS = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel [])

allowSD :: SLIO User Rel Rep ()
allowSD = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st ++ [(User "Sanitizer", User "DB")])

escape :: Labeled User String -> SLIO User Rel Rep (Labeled User String)
escape input= toLabeled (User "Sanitizer") $ do 
    i <- traceShow "relabel" $ asNT unlabel input
    -- i <- traceShow "relabel" $  unlabel input
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

timetransitive2 :: SLIO User Rel Rep String
timetransitive2 = do
    input <- label (User "Input") "malicious code"
    --xx <- unlabel input
    --x <- relabel input Sanitizer
    x <- escape input
    l <- getLabel
    traceShow l disallowIS
    traceShow x allowSD
--    xx <- unlabel x
    db <- relabel x (User "DB")
--    xx <- unlabel x
    unlabel db
    l <- getLabel
    traceShow l $ unlabel db 

main :: IO ()
main = do
    (r, s) <- unSLIO timetransitive2 initState
    print r
    print s