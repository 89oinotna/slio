{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Main
  ( main
  ) where

import           Debug.Trace

import           SimpleStLIO

import           Data.List                      ( (\\)
                                                , groupBy
                                                , nub
                                                )
import           Data.Map                       ( elems
                                                , empty
                                                , insert
                                                , lookup
                                                )
import           SimpleStLIOUtil
import Control.Monad (when)
import qualified Data.HashMap.Strict           as HM
import Impl


initState :: LIOState User Rel (Rep)
initState =LIOState
  { lcurr = HM.empty
  , scurr = Rel [(User "NSA", User "Military")]
  , ntlab = HM.empty
  , assocnt = HM.empty
  , rlab  = Rep HM.empty
  , newid = 0
  }

disallowNM :: SLIO User Rel (Rep) ()
disallowNM = do
  rel <- getState
  let (Rel st) = rel
  setState (Rel $ st \\ [(User "NSA", User "Military")])

disallowMB :: SLIO User Rel (Rep) ()
disallowMB = do
  rel <- getState
  let (Rel st) = rel
  setState (Rel $ st \\ [(User "Military", User "Bob")])

allowMB :: SLIO User Rel (Rep) ()
allowMB = do
  rel <- getState
  let (Rel st) = rel
  setState (Rel $ st ++ [(User "Military", User "Bob")])

allowNM :: SLIO User Rel (Rep) ()
allowNM = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st ++ [(User "NSA", User "Military")])


leak :: SLIO User Rel Rep Integer
leak = do
  file1 <- label (User "NSA") 0
  r <- newLIORef (User "Bob") 1

  --file  <- unlabel file1
  --mil   <- newLIORef (User "Military") file
  --writeLIORef mil 1
  _ <- toLabeled (User "NSA") ( do
    
    file  <- asRP unlabel [User "Military"] file1
    --disallowNM
    when (file==0) (do
      allowMB
      writeLIORef r 0))
  readLIORef r

rptt :: SLIO User Rel Rep Integer
rptt = do
  file <- label (User "NSA") 0
  x <- toLabeled (User "Military") $ do
                  asRP (asNT unlabel) [User "Military"] file
  disallowNM
  allowMB
  b <- relabel file (User "Bob") 
  unlabel b
   
secure :: SLIO User Rel Rep Integer
secure = do
  n <- label (User "NSA") 0
  m <- toLabeled (User "Military") $ do
        asRP (unlabel) [User "Military"] n
  disallowNM
  allowMB
  relabel n (User "Bob") 
  return 0
  --unlabel b

main :: IO ()
main = do
  (r, s) <- unSLIO secure initState
  print r
  print s
