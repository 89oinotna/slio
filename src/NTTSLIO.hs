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
module NTTSLIO where



import qualified Control.Monad.State.Class     as State
import           Control.Monad.State.Strict
                                         hiding ( get
                                                , guard
                                                , modify
                                                , put
                                                )

import           Control.Applicative
--import Data.Biapplicative
import           Prelude                 hiding ( fail )

import qualified Data.HashMap.Strict           as HM
import           Data.Hashable
import           Data.List                      ( nub )
import qualified Data.List                     as List
import           IFC
-- the bool in rlab tracks the fact that a global unlabel has been done
-- the guard has to check that any info in the computation (unlabeled) can flow to the label 
-- we can replay information only if there wasnt any global unlabeling or if all of the replaying (all the ids from 0 to current) can flow to the label
data NTTState l = NTTState
  { ntlab   :: HM.HashMap l [Int]
  , assocnt :: HM.HashMap (l, Int) (HM.HashMap l [Int])
  }--, ids :: Map String Int }
  deriving Show

type NTTSLIO l m a = StateT (NTTState l) m a -- => s -> ((s' => (a,s')),s)

class (Eq l, Hashable l) => HasNT st l | st -> l where
  getNTLab :: st -> HM.HashMap l [Int]
  setNTLab :: HM.HashMap l [Int] -> st -> st
  getNTAssoc :: st -> HM.HashMap (l, Int) (HM.HashMap l [Int])
  setNTAssoc :: HM.HashMap (l, Int) (HM.HashMap l [Int]) -> st -> st
  modifyNTLab :: (HM.HashMap l [Int] -> HM.HashMap l [Int]) -> st -> st
  modifyNTLab f st = setNTLab (f (getNTLab st)) st
  modifyNTAssoc :: (HM.HashMap (l, Int) (HM.HashMap l [Int]) -> HM.HashMap (l, Int) (HM.HashMap l [Int])) -> st -> st
  modifyNTAssoc f st = setNTAssoc (f (getNTAssoc st)) st

instance (Eq l, Hashable l) => HasNT (NTTState l) l where
  getNTLab = ntlab
  setNTLab nt s = s { ntlab = nt }
  getNTAssoc = assocnt
  setNTAssoc ass s = s { assocnt = ass }

class (Monad m, HasNT nt l) => MonadNTT nt l m | m -> nt l where
  asNT :: LV t l
    => (t l a -> m a)
    -> t l a
    -> m a
  getNTState :: m nt
  putNTState :: nt -> m ()
  modifyNTState :: (nt -> nt) -> m ()

instance (Monad m, HasNT (NTTState l) l) => MonadNTT (NTTState l) l (StateT (NTTState l) m) where
  asNT f ld = do
    taintNT (getLabel' ld) (getId' ld)
    f ld
  getNTState    = State.get
  putNTState    = State.put
  modifyNTState = State.modify

instance (MonadIFC st scurr rel l m, MonadNTT (NTTState l) l (StateT (NTTState l) m))
  => MonadIFC st scurr rel l (StateT (NTTState l) m) where
  label l a = guard l >> labelInternal l a
              --guard l>> incAndGetId >>= return . (Lb l a)
  labelInternal l a = do
    x <- lift (labelInternal l a)
    addAssocNt (getLabel' x) (getId' x)
    return x
  unlabel lv@(Lb l _ i) = do
    nt <- HM.lookupDefault HM.empty (l, i) . getNTAssoc <$> State.get
    State.modify $ modifyNTLab (HM.unionWith List.union nt)
    lift $ modify $ modifyLSet (HM.unionWith List.union nt)
    lift $ unlabel lv -- taint l i >> return a
  guard l = lift $ guard l
    -- do
    -- lc <- getLSet <$> (lift get)
    -- rel <- getRelation
    -- let checkPassed = and [ lrt rel x l | x <- HM.keys lc ]
    -- unless checkPassed (fail "label check failed")
    -- do
    --     s <- lift get
    --     when ( any (incUpperSet (getRel s) rel )
    --             $ HM.keys (getLSet s)
    --         ) (fail "incUpperClosure check failed")
    --     lift . put $ setRel rel s
  getRelation  = lift getRelation -- getRel <$> (lift get)



  get          = lift get
  put          = lift . put
  modify       = lift . modify
  setUserState = lift . setUserState
  resetOP      = do
    s  <- getNTState
    rs <- lift resetOP
    return
      (do
        ns <- getNTState
        putNTState $ setNTAssoc (getNTAssoc ns) s
        lift rs
      )
  toLabeled l m = do
    rop <- resetOP
    x   <- m
    -- guard l
    lv  <- label l x
    rop
    return lv

  newIORefInternal l a = do
    x <- lift $ newIORefInternal l a
    addAssocNt (getLabel' x) (getId' x)
    return x

  newIORef l a = guard l >> newIORefInternal l a
  readIORef lv = do
      nt <- HM.lookupDefault HM.empty (getLabel' lv, getId' lv) . getNTAssoc <$> State.get
      State.modify $ modifyNTLab (HM.unionWith List.union nt)
      lift $ modify $ modifyLSet (HM.unionWith List.union nt)
      lift $ readIORef lv

  writeIORef lv b = guard (getLabel' lv) >> writeIORefInternal lv b
  
  writeIORefInternal lv b = do
      nt <- HM.lookupDefault HM.empty (getLabel' lv, getId' lv) . getNTAssoc <$> State.get
      State.modify $ modifyNTLab (HM.unionWith List.union nt)
      lift $ modify $ modifyLSet (HM.unionWith List.union nt)
      lift $ writeIORefInternal lv b


taintNT :: (Eq l, Hashable l, HasNT nt l, MonadNTT nt l m) => l -> Int -> m ()
taintNT l i = modifyNTState $ modifyNTLab (insert l i)

addAssocNt :: (HasNT nt l, Monad m, MonadNTT nt l m) => l -> Int -> m ()
addAssocNt l i = modifyNTState $ \s -> modifyNTAssoc
  (HM.insertWith (HM.unionWith List.union)
                 (l, i)
                 (getNTLab s)
  )
  s

insert
  :: (Hashable k, Eq a, Eq k) => k -> a -> HM.HashMap k [a] -> HM.HashMap k [a]
insert k v m = case HM.lookup k m of
  Nothing -> HM.insert k [v] m
  Just xs -> HM.insert k (nub $ v : xs) m


