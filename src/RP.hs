{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FunctionalDependencies #-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module RP 
    where



import qualified Control.Monad.State.Class as State
import Control.Monad.State.Strict hiding (guard, get, put, modify)

import           Control.Applicative
import           Prelude                 hiding ( fail )

import Data.List ( nub )
import qualified Data.List as List
import qualified Data.HashMap.Strict as HM
import Data.Hashable
import IFC

-- the bool in rlab tracks the fact that a global unlabel has been done
-- the guard has to check that any info in the computation (unlabeled) can flow to the label 
-- we can replay information only if there wasnt any global unlabeling or if all of the replaying (all the ids from 0 to current) can flow to the label
-- newtype RPState r l = RPState { rp :: r }--, ids :: Map String Int }
--   deriving Show

-- type RPSLIO r l m a = StateT (RPState r l) m a -- => s -> ((s' => (a,s')),s)

-- class HasRP st r l  | st -> r l where
--   getRP :: st -> r
--   setRP :: r -> st -> st
--   modifyRP :: (r -> r) -> st -> st
--   modifyRP m st = setRLab (m (getRLab st)) st

-- instance HasRP (RPState r l) r l where
--   getRP = rp
--   setRP rl s = s { rp = rl }
newtype RPState l = RPState {r::HM.HashMap l [(l, Int, l, Bool)] }

class (Monad m) => MonadRP rp l m | m -> rp l where
  asRP :: LV t l
    => (t l a -> m a)
    -> t l a
    -> [l]
    -> m a
  getRPState :: m rp
  putRPState :: rp -> m ()
  modifyRPState :: (rp -> rp) -> m ()

instance (Monad m) => MonadRP (RPState l)  l (StateT (RPState l) m) where
  asRP f ld lst = do
    addPromises (getLabel' ld) (getId' ld) lst
    f ld
  getRPState = State.get
  putRPState = State.put
  modifyRPState = State.modify

instance (MonadIFC st scurr rel l m, MonadRP (RPState l) l (StateT (RPState l) m))
  => MonadIFC st scurr rel l (StateT (RPState l) m) where
  label l a = do 
              x <- lift (label l a) 
              enableRP l
              return x--guard l>> incAndGetId >>= return . (Lb l a)
  unlabel lv@(Lb l _ i) = lift $ unlabel lv -- taint l i >> return a
  guard l = lift $ guard l
  
  getRelation = lift getRelation -- getRel <$> (lift get)

  toLabeled l m = do
    x <- m
    label l x
  get = lift get
  put = lift . put
  modify = lift . modify
  setUserState scurr = do
    oldRel <- getRelation
    s <- get
    put $ setScurr scurr s
    newRel <- getRelation
    when ( any (incUpperSet (oldRel) (newRel) )
                $ HM.keys (getLSet s)
            ) (fail "incUpperClosure check failed")
    



insert
  :: (Hashable k, Eq a, Eq k) => k -> a -> HM.HashMap k [a] -> HM.HashMap k [a]
insert k v m = case HM.lookup k m of
  Nothing -> HM.insert k [v] m
  Just xs -> HM.insert k (nub $ v : xs) m
    

