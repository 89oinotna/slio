{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil

import Data.List ((\\))
import SimpleStLIO (newLIORef, writeLIORef, readLIORef, unlabel)
import qualified Data.HashMap.Strict           as HM
import Impl

initState :: LIOState User Rel Rep 
initState = LIOState { lcurr = HM.empty
                     , scurr = Rel [(User "Data", User "App")]
                     , ntlab = HM.empty
  , rlab  = Rep HM.empty
  , newid = 0
  }

disallowDA :: SLIO User Rel Rep  ()
disallowDA = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel [])

directRelease :: SLIO User Rel Rep  String
directRelease = do
    dat <- label (User "Data" ) "data"
    disallowDA
    -- udat <- unlabel dat
    -- o <- newLIORef App udat
    -- readLIORef o
    ad <- relabel dat (User "App")
    unlabel ad


main :: IO ()
main = do
    (r, s) <- unSLIO directRelease initState
    print r
    print s