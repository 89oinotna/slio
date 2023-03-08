{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}

module Main
  ( main
  ) where
import Data.IORef ( newIORef, readIORef, writeIORef, IORef )
import           Debug.Trace

import           SimpleStLIO

import           Control.Monad                  ( when )
import qualified Data.HashMap.Strict           as HM
import           Data.Hashable
import           Data.List                      ( (\\)
                                                , groupBy
                                                , nub
                                                )
import qualified Data.List                     as List
import           Data.Map                       ( elems
                                                , empty
                                                , lookup
                                                )
import           SimpleStLIOUtil
import Impl


initState :: LIOState User Rel (Rep)
initState = LIOState
  { lcurr = HM.empty
  , scurr = Rel
              [(User "NSA", User "Military"), (User "Military", User "Another")]
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



replaying :: SLIO User Rel (Rep) String
replaying = do
  file1 <- label (User "NSA") "secret"
  --file2 <- label (User "NSA") "secret 2"
  --file  <- unlabelReplaying file1 [User "Another"]
  --file  <- unlabelReplaying file1 [User "Military"] -- what if instead of file1 this is file2 ??
  -- file <- asRP (Left unlabel) [User "Military"]  (Left file1)
  file <- asRP ( unlabel) [User "Military"]  ( file1)
  --lst <- getReplaying
  --file  <- unlabel file1
  mil   <- newLIORef (User "Military") file
  --writeLIORef mil ""
  disallowNM
  writeLIORef mil ""
  --mil   <- newLIORef (User "Military") file
  -- mil   <- newLIORef (User "Another") $ file++"A"
  --writeLIORef mil file
  readLIORef mil

-- ______________________
-- This example shows why using relable is not the correct solution

unlabelAsReplaying
  :: (Label l st r, Replaying r l st) => Labeled l a -> l -> SLIO l st r a
unlabelAsReplaying ldata nl = do
  d <- relabel ldata nl
  unlabel d

replaying2 :: SLIO User Rel (Rep) String
replaying2 = do
  file <- label (User "NSA") "secret"
  file <- unlabelAsReplaying file (User "Military") --wrong
  --file <- unlabel file
  mil  <- newLIORef (User "Military") file
  an   <- newLIORef (User "Another") file
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
