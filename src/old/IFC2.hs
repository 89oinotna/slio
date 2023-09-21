{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TupleSections          #-}

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
module IFC
  ( MonadIFC(..)
  , HasLSet(..)
  , HasLVIds(..)
--   , HasRelation(..)
  , HasScurr(..)
  , ToRelation(..)
  , Relation(..)
  , MutableRelation(..)
  , Labeled(..)
  , LIORef(..)
  , LV(..)
  ) where



-- import Control.Monad.Trans.State.Strict
import           Control.Monad.State.Strict
                                         hiding ( get
                                                , guard
                                                , put
                                                )

--import Data.Biapplicative

import           Prelude                 hiding ( fail )

-- import           Debug.Trace                    ( traceShow )
import qualified Data.HashMap.Strict           as HM
import           Data.HashSet
import           Data.Hashable
import           Data.IORef                     ( IORef )
import Data.Type.Equality ((:~:), type (==))
import Control.Monad.State (get)


class HasLSet st l | st -> l where
  getLSet :: st -> HM.HashMap l [Int]
  setLSet :: HM.HashMap l [Int] -> st -> st
  modifyLSet :: (HM.HashMap l [Int] -> HM.HashMap l [Int]) -> st -> st
  modifyLSet m st = setLSet (m (getLSet st)) st

class HasLVIds st where
  getId :: st -> Int
  setId :: Int -> st -> st
  incId :: st -> st

-- class Relation rel l => HasRelation st rel l | st l -> rel  where
--   getRel :: st l -> rel l
--   setRel :: rel l -> st rel l -> st rel l

class HasScurr st scurr | st -> scurr where
  getScurr :: st -> scurr
  setScurr :: scurr -> st -> st

class (Eq l, Show l, Hashable l) => Relation rel l where
  lrt :: rel l -> l -> l -> Bool-- rel -> l -> l -> Bool --
  getElements :: rel l -> HashSet l

class Relation rel l => MutableRelation rel l where
  incUpperSet :: rel l -> rel l -> l -> Bool
  incUpperSet oldRel newRel l=any (\el -> not (lrt oldRel l el) &&  lrt newRel l el) (getElements newRel)
  union :: rel l -> rel l -> rel l

class Relation rel l => ToRelation state rel l | state -> rel l where
    toRelation :: state -> rel l

class SLIO scurr rel l m where
    setUserState :: scurr -> m ()

class
    (
    Relation rel l, HasLSet st l,
    HasLVIds st, MonadFail m, MonadIO m
    )
    => MonadIFC st rel l m | m ->st where

  label ::  l -> a -> m (Labeled l a)

  label' :: l -> a -> m (Labeled l a)

  unlabel ::  Labeled l a -> m a

  guard ::  l -> m ()

  getRelation ::  m (rel l)

  toLabeled ::  l -> m a -> m (Labeled l a)

  resetOP :: m (m ())

  readIORef ::  LIORef l a -> m a

  writeIORef ::  LIORef l a -> a -> m ()

  newIORef ::  l -> a -> m (LIORef l a)

  newIORef' ::  l -> a -> m (LIORef l a)

  writeIORef' ::  LIORef l a -> a -> m ()

  -- User must not use those functions
--   get :: m (st l)
--   put :: st  l -> m ()
--   modify :: (st  l -> st  l) -> m ()

data IFCState l = IFCState
  { lset  :: HM.HashMap l [Int]
  , newid :: Int
  }
  deriving Show

instance HasLSet (IFCState l) l where
  getLSet = lset
  setLSet lset' st = st { lset = lset' }
  modifyLSet m st = setLSet (m (getLSet st)) st

instance HasLVIds (IFCState l) where
  getId = newid
  setId newid' st = st { newid = newid' }
  incId st = setId (getId st + 1) st

instance (MonadIO m, MonadFail m, Relation rel l) => (MonadIFC (IFCState l) rel l (StateT (IFCState l) m)) where
  label l a= guard l >> label' l a
  label' l a= incAndGetId >>= return . (Lb l a)
  unlabel = taint
  guard = _
  getRelation = _
  toLabeled = _
  resetOP = _
  readIORef = _
  writeIORef = _
  newIORef = _
  newIORefInternal = _
  writeIORefInternal = _

-- instance (MonadIFC st rel l m, SLIO scurr rel l m, (st == scurr) ~ False) => MonadIFC st rel l (StateT scurr m) where


data Labeled l a = Lb
  { labelOf :: l
  , valueOf :: a
  , idOf    :: Int
  }
  deriving (Eq, Show)

data LIORef l a = LIORef
  { labelOfRef :: l
  , _lioRefVal :: IORef a
  , lioRefInt  :: Int
  }


class LV t l where
  getLabel' :: t l a -> l
  getId'    :: t l a -> Int

instance LV LIORef l  where
  getLabel' = labelOfRef
  getId'    = lioRefInt

instance LV Labeled l  where
  getLabel' = labelOf
  getId'    = idOf


incAndGetId
  :: (Monad m, HasLVIds st, MonadIFC st rel l m, MonadState st m) => m Int
incAndGetId = do
  s <- get
  modify incId
  return $ getId s

-- taint
--   :: (Eq l, Hashable l, HasLSet (st scurr l) l, MonadIFC st scurr rel l m)
--   => l
--   -> Int
--   -> m ()
-- taint l i = modify $ modifyLSet (insert l i)

-- insert
--   :: (Hashable k, Eq a, Eq k) => k -> a -> HM.HashMap k [a] -> HM.HashMap k [a]
-- insert k v m = case HM.lookup k m of
--   Nothing -> HM.insert k [v] m
--   Just xs -> HM.insert k (nub $ v : xs) m


