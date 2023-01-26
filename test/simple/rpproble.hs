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
              [(User "NSA", User "Military"), (User "B", User "NSA")]
  , ntlab = HM.empty
  , rlab  = Rep HM.empty
  , newid = 0
  }

disallowNM :: SLIO User Rel (Rep) ()
disallowNM = do
  rel <- getState
  let (Rel st) = rel
  setState (Rel $ st \\ [(User "NSA", User "Military")])


replaying :: SLIO User Rel (Rep) ()
replaying = do
  f1 <- newLIORef (User "NSA") "secret"
  f2 <- label (User "B") "secret"
  _ <- toLabeled (User "Military") $ do
        s <- asRP ( readLIORef) [User "Military"]  (f1)
        label (User "Military") s
  disallowNM
  y <- toLabeled (User "NSA") $ do
            xx <- unlabel f2
            writeLIORef f1 xx
  return ()
 -- z <- readLIORef f1
  --label (User "Military") z
  --y <- unlabel file2
  --return y
--   z <- label (User "Military") ""
--   unlabel z
  

main :: IO ()
main = do
  (r, s) <- unSLIO replaying initState
  --print r
  print s
