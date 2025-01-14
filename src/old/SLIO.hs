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
import Data.IORef (readIORef, newIORef, writeIORef)

type Lset l = HM.HashMap l [Int]

data SLIOState scurr l = SLIOState
  { lset  :: Lset l
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


-- class (Monad m, ToRelation scurr rel l) => MonadSLIO scurr rel l m | m -> scurr l where 
--   getSLIOState :: m scurr
--   putSLIOState :: scurr -> m ()
--   modifySLIOState :: (scurr -> scurr) -> m ()


-- -- instance (Monad io, ToRelation scurr rel l, HasScurr (SLIOState scurr l) scurr,
--       MutableRelation rel l, HasLSet (SLIOState scurr l) l, MonadFail io)
--   => MonadSLIO scurr rel l (StateT (SLIOState scurr l) io) where
--     getSLIOState = getScurr <$> State.get
--     putSLIOState newState = do
--       s <- State.get
--       when
--         ( any (incUpperSet (toRelation $ getScurr s) (toRelation newState))
--         $ HM.keys (getLSet s)
--         )
--         (fail "incUpperClosure check failed")
--       State.put $ setScurr newState s

instance (MonadIO io, MutableRelation rel l, HasLSet (SLIOState scurr l) l,
      HasScurr (SLIOState scurr l) scurr, ToRelation scurr rel l,
  HasLVIds (SLIOState scurr l), MonadFail (StateT (SLIOState scurr l) io))
  => MonadIFC (SLIOState scurr l) scurr rel l (StateT (SLIOState scurr l) io) where
  label l a = guard l >> labelInternal l a
  labelInternal l a = incAndGetId >>= return . (Lb l a)
  unlabel (Lb l a i) = taint l i >> return a

  guard l = do
    lc  <- getLSet <$> get
    check lc l

  
  getRelation lset= toRelation . getScurr <$> get
  setUserState newState = do
    s <- get
    when
      ( any (incUpperSet (toRelation $ getScurr s) (toRelation newState))
      $ HM.keys (getLSet s)
      )
      (fail "incUpperClosure check failed")
    State.put $ setScurr newState s
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


  toLabeled l m = do
    rop <- resetOP
    x   <- m
    -- guard l
    lv  <- label l x
    rop
    return lv

  readIORef (LIORef l a i) = taint l i >> liftIO (Data.IORef.readIORef a)

  newIORef l a = guard l >> newIORefInternal l a

  newIORefInternal l a = do
    i <- incAndGetId
    ref <- liftIO (Data.IORef.newIORef a) 
    return (LIORef l ref i)

  writeIORef lv@(LIORef l a i) b = guard l >> writeIORefInternal lv b

  writeIORefInternal (LIORef l a i) b = liftIO (Data.IORef.writeIORef a b)

incAndGetId
  :: (Monad m, HasLVIds st, MonadIFC st scurr rel l m) => m Int
incAndGetId = do
  s <- get
  modify incId
  return $ getId s

taint
  :: (Eq l, Hashable l, HasLSet st l, MonadIFC st scurr rel l m)
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
