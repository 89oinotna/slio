{-# LANGUAGE MultiParamTypeClasses #-}
module TwoPoint
  ( SecLevel(..)
  , initState
  ) where

import SimpleStLIO

data SecLevel = High | Low
  deriving (Eq)

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
