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
module SLIO
  ( SLIO
  -- , Labeled
  -- , LIORef
  -- , getLSet'
  -- , getState'
  -- , setState
  , SLIOState(..)
  ) where



-- import Control.Monad.Trans.State.Strict
import qualified Control.Monad.State.Class     as State
import           Control.Monad.State.Strict
                                         hiding ( get
                                                , guard
                                                , modify
                                                , put
                                                )

--import Data.Biapplicative
import           Control.Applicative

import           Prelude                 hiding ( fail )

-- import           Debug.Trace                    ( traceShow )
import qualified Data.HashMap.Strict           as HM
import           Data.Hashable
import           Data.List                      ( nub )
import           IFC

data SLIOState scurr l = SLIOState
  { lset  :: HM.HashMap l [Int]
  , scurr :: scurr
  , newid :: Int
  }
  deriving Show

type SLIO l scurr io a = StateT (SLIOState scurr l) io a

instance HasScurr (SLIOState scurr l) scurr  where
  getScurr = scurr
  setScurr sc s = s { scurr = sc }
  -- modifyScCurr :: (scurr -> scurr) -> st -> st
  -- modifyScCurr m st = setScCurr (m (getScCurr st)) st


instance HasLSet (SLIOState rel l) l where
  getLSet = lset
  setLSet ls s = s { lset = ls }

instance HasLVIds (SLIOState rel l) where
  getId = newid
  setId i s = s { newid = i }
  incId s = s { newid = succ $ newid s }

-- instance Relation rel l => HasRelation SLIOState rel l where
--   getRel = scurr
--   setRel rel st = st { scurr = rel }


instance (MonadIO io, MutableRelation rel l, HasLSet (SLIOState scurr l) l,
      HasScurr (SLIOState scurr l) scurr, ToRelation scurr rel l,
  HasLVIds (SLIOState scurr l), MonadFail (StateT (SLIOState scurr l) io))
  => MonadIFC SLIOState scurr rel l (StateT (SLIOState scurr l) io) where
  label l a = guard l >> labelInternal l a
  labelInternal l a = incAndGetId >>= return . (Lb l a)
  unlabel (Lb l a i) = taint l i >> return a
  guard l = do
    lc  <- getLSet <$> get
    rel <- getRelation
    let checkPassed = and [ lrt rel x l | x <- HM.keys lc ]
    unless checkPassed (fail "label check failed")
  setUserState newState = do
    s <- get
    when
      ( any (incUpperSet (toRelation $ getScurr s) (toRelation newState))
      $ HM.keys (getLSet s)
      )
      (fail "incUpperClosure check failed")
    State.put $ setScurr newState s
  getRelation = toRelation . getScurr <$> get
  -- toLabeled l m = do
  --   s1  <- get
  --   x <- m
  --   guard l
  --   id <- incAndGetId
  --   put $ setId id s1
  --   return $ Lb l x id
  get         = State.get
  put         = State.put
  modify      = State.modify
  resetOP     = do
    s <- get
    return
      (do
        ns <- get
        put $ setId (getId ns) s
      )
  -- toLabeledOP l x = do

  toLabeled l m = do
    rop <- resetOP
    x   <- m
    -- guard l
    lv  <- label l x
    rop
    return lv

    -- id <- incAndGetId
    -- return $ Lb l x id

incAndGetId
  :: (Monad m, HasLVIds (st scurr l), MonadIFC st scurr rel l m) => m Int
incAndGetId = do
  s <- get
  modify incId
  return $ getId s

taint
  :: (Eq l, Hashable l, HasLSet (st scurr l) l, MonadIFC st scurr rel l m)
  => l
  -> Int
  -> m ()
taint l i = modify $ modifyLSet (insert l i)

insert
  :: (Hashable k, Eq a, Eq k) => k -> a -> HM.HashMap k [a] -> HM.HashMap k [a]
insert k v m = case HM.lookup k m of
  Nothing -> HM.insert k [v] m
  Just xs -> HM.insert k (nub $ v : xs) m

-- relabel
--   :: (MonadIFC st rel l (StateT (st rel l) io), Pre (StateT (st rel l) io) l) 
--   => Labeled l a
--   -> l
--   -> StateT (st rel l) io (Labeled l a)
-- relabel lblVal lbl = toLabeled lbl (unlabel lblVal)

-- relabel
--   :: (MonadIFC st rel l m) --, Pre m l) 
--   => Labeled l a
--   -> l
--   -> m (Labeled l a)
-- relabel lblVal lbl = toLabeled lbl (unlabel lblVal)
