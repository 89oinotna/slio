{-# LANGUAGE MultiParamTypeClasses #-}
-- | This module demonstrates why the 'incUpperSet' check is necessary, as
-- explained in the paper on Stateful LIO.
module Main where

import SimpleStLIO
import SimpleStLIOUtil

import Control.Monad (when)

data SecLevel = High | Low
  deriving (Eq, Show)

instance Label SecLevel Bool where
  -- | Information flow from High to Low only allowed iff bool is set to True.
  lrt hToL High Low  =  hToL
  lrt hToL _    _    =  True
  -- | Thus only increasing upper set possible for High, and only when changing
  -- bool from False to True.
  incUpperSet False True High  =  True
  incUpperSet _     _    _     =  False

initState :: LIOState SecLevel Bool
initState = LIOState { lcurr = []
                     , scurr = False
                     }

-- | This program triggers an error when trying to set the state to true, i.e.
-- when highData is initialised to 0. The rationale is otherwise this program
-- can be used to leak the value of High data in a Low reference, without
-- passing by the "setState True" command. The 'incUpperSet' check transforms
-- this into a leak via progress (or: termination).
leak :: SLIO SecLevel Bool Int
leak = do
  highData <- label High 42
  lowRef   <- newLIORef Low 1
  _ <- toLabeled High $ do
    h <- unlabel highData
    when (h == 0) (setState True >> writeLIORef lowRef 0)
  readLIORef lowRef


main :: IO ()
main = do
  (r, s) <- unSLIO leak initState
  putStrLn $ "Result:        " ++ show r

