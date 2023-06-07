
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
module NWL (
  NWLState(..),
  MonadNWL(..)
)
 where



import           Control.Monad.State.Strict
                                         hiding ( get
                                                , guard
                                                , modify
                                                , put
                                                )

import           Control.Applicative
import           Prelude                 hiding ( fail )

import qualified Data.HashMap.Strict           as HM
import           Data.Hashable
import           Data.List                      ( intersect )
import qualified Data.List                     as List
import           IFC
import qualified Data.HashSet as HashSet
import qualified Control.Monad.State as State



data NWLState l = NWLState {
    lset :: HM.HashMap l [Int],
    derivable:: HM.HashMap l (HM.HashMap (l,Int) [(l, Int)]) }
    deriving Show

class (Monad m) => MonadNWL wl l m | m -> wl l where
    asNWL ::LV t l =>  m (t l a) -> m (t l a)
    getNWLState :: m wl
    putNWLState :: wl -> m ()


instance (Monad m, Hashable l, Eq l) => MonadNWL (NWLState l) l (StateT (NWLState l) m) where
    asNWL m = do
      lv <- m
      s <- getNWLState
      let ll = HashSet.fromList (concatMap (\(k, v) -> map (k,) v) (HM.toList (lset s))) -- all the labels that are in the lset
      let derivl = HM.lookupDefault HM.empty (getLabel' lv) (derivable s) -- all the derivable labels for the current label
      let newDerivl = HashSet.foldl' (\acc (l,i) -> HM.insertWith List.union (l,i) (HashSet.toList $ HashSet.delete (l,i) ll) acc) derivl ll -- for each label in ll, add all the other labels to the derivable map
      putNWLState $ s {derivable = HM.insert (getLabel' lv) newDerivl (derivable s)} 
      return lv
    getNWLState = State.get
    putNWLState = State.put

instance (MonadIFC st scurr rel l m, MonadNWL (NWLState l) l (StateT (NWLState l) m))
  => MonadIFC st scurr rel l (StateT (NWLState l) m) where
  label l a = guard l >> labelInternal l a
  labelInternal l a = lift $ labelInternal l a

  unlabel = lift . unlabel

  guard l = do
    
    lc  <- getLSet <$> get
    -- for all derivable lv  create an lset containing only it -> getRelation -> check
    s <- get
    derivablel <- HM.lookupDefault HM.empty l . derivable <$> getNWLState

    let toCheck = concatMap (\(k, v) -> map (k,) v) (HM.toList lc) `intersect` (HM.keys derivablel)
    mapM_ (\k -> do
          -- s <- get
          let nwl = map (\(ll,i) -> (ll, [i])) $ HM.lookupDefault [] k derivablel -- get the derivable labels for the current label
          let newlset = HM.fromListWith (++) nwl -- create a new lset containing only the derivable labels
          put (setLSet newlset s) -- set the new lset 
          lift $ guard l
          -- fail ("guard " ++ show l ++ " failed")
          ) toCheck
    put $ setLSet lc s

  getRelation = lift getRelation

  get    = lift get
  put  s  = do
    NWLState _ derivable <- getNWLState
    putNWLState $ NWLState (getLSet s) derivable
    lift $ put s

  modify s= do
    lift $ modify s
    lset <- getLSet <$> get
    NWLState _ derivable <- getNWLState
    putNWLState $ NWLState lset derivable

  setUserState = lift . setUserState

  resetOP = do
    rs <- lift resetOP
    return
      (do
        lift rs
        s <- get
        NWLState _ derivable <- getNWLState
        putNWLState $ NWLState (getLSet s) derivable
        )

  toLabeled l m = do
    rop <- resetOP
    x   <- m
    lv  <- label l x
    rop
    return lv

  newIORefInternal l a = lift (newIORefInternal l a)

  newIORef l a = guard l >> newIORefInternal l a

  writeIORefInternal lv b = lift (writeIORefInternal lv b)

  writeIORef lv b = guard (getLabel' lv) >> writeIORefInternal lv b

  readIORef = lift . readIORef

