{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil

import Data.List ((\\))
import SimpleStLIO (newLIORef, writeLIORef, readLIORef, unlabel)
import Data.Bits (Bits(xor))
import qualified Data.HashMap.Strict           as HM
import Impl



initState :: LIOState User Rel Rep
initState = LIOState
  { lcurr = HM.empty
  , scurr = Rel [((User "Secret" ),(User "Pub" )), ((User "Key"), (User "Pub" ))]
  , ntlab = HM.empty
  , rlab  = Rep HM.empty
  , newid = 0
  }

disallowSP :: SLIO User Rel Rep ()
disallowSP = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st \\ [((User "Secret" ) , (User "Pub" ))])

whitelisting :: SLIO User Rel Rep  String
whitelisting = do
    secret <- label (User "Secret" ) "secret"
    k <- label (User "Key" ) "key"
    secret <- unlabel secret
    k <- unlabel k
    pub <- newLIORef (User "Pub" ) (k ++ secret)
    disallowSP
    writeLIORef pub k
    traceShow "disallowing" $readLIORef pub


main :: IO ()
main = do
    (r, s) <- unSLIO whitelisting initState
    print r
    print s