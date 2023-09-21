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
-- {-# LANGUAGE UndecidableInstances #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}
module DypIFC(
    IFC(
        label,
        unlabel,
        toLabeled,
        setPolicy,
        getPolicy,
        getLSet
    )
  , HasLSet(..)
  , HasId(..)
--   , HasRelation(..)
  , HasPolicy(..)
  , Rel(..)
  , Policy(..)
  , Labeled(..)
  , Lset 
  , Id
  , IFCInternal(..)
) where

import           Control.Monad.State.Strict
                                         hiding ( guard
                                                )

--import Data.Biapplicative
import           Prelude                 hiding ( fail )
import Data.HashSet
import Data.Hashable

type Id = Int

data Labeled l a = LB l a Id

-- class Lset lset l where
--     isin :: l -> Id -> lset -> Bool

type Lset l = HashSet (l, Id)

class HasLSet st l | st -> l where
  getLSet' :: st -> Lset l
  setLSet' :: Lset l -> st -> st
  modifyLSet' :: (Lset l -> Lset l) -> st -> st
  modifyLSet' f st = setLSet' (f (getLSet' st)) st

class HasPolicy st ps | st -> ps where
  getPolicy' :: st -> ps
  setPolicy' :: ps -> st -> st
  modifyPolicy' :: (ps -> ps) -> st -> st
  modifyPolicy' f st = setPolicy' (f (getPolicy' st)) st

class HasId st where
  getId :: st -> Id
  setId :: Id -> st -> st
  incId :: st -> st

class (Eq l, Hashable l, MonadState st m, MonadFail m
    , IFCInternal l st ps)
 => IFC l st ps  m | m -> st ps  l where
    label :: l -> a -> m (Labeled l a)
    label l v = do
        st <- get
        unless (guard l st) (fail "label check failed")
        put (incId st)
        return $ LB l v (getId st)
    unlabel :: Labeled l a -> m a
    unlabel (LB l e i) = do
        st <- get
        put $ opUnlabel l i (modifyLSet' (insert (l,i)) st)
        return e
    toLabeled :: l -> m a -> m (Labeled l a)
    toLabeled l m = do
        st <- get
        e <- m
        toLabeledRet st l e
    setPolicy :: ps -> m ()
    setPolicy ps = do
        st <- get
        let st' = opState st ps
        if stateGuard st ps st' then fail "state guard fail"
        else put st'
    getPolicy :: m ps
    getPolicy = do
        getPolicy' <$> get
    getLSet ::  m (Lset l)
    getLSet = do
        getLSet' <$> get
    -- Hidden
    toLabeledRet :: st -> l -> a -> m (Labeled l a)
    toLabeledRet st0 l e = do
        st <- get
        unless (guard l st) (fail "label check failed")
        put (opToLabeledRet st l (getId st) st0)
        return $ LB l e (getId st)

class Rel rel l where
    lrt :: l -> l -> rel -> Bool

class Policy ps l where
    canflow :: l -> i -> l -> ps -> Bool

class (Policy ps l, HasLSet st l
    , HasId st, HasPolicy st ps) => IFCInternal l st ps | st -> ps l where
    guard :: l -> st -> Bool
    stateGuard :: st -> ps -> st -> Bool
    opState :: st -> ps -> st
    opLabel :: l -> i -> st -> st
    opUnlabel :: l -> i -> st -> st
    opToLabeledRet :: st -> l -> i -> st -> st

