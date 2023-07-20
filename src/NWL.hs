
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
import           Data.List                      ( intersect, foldl', union, nub )
import qualified Data.List                     as List
import           IFC
import qualified Data.HashSet as HashSet
import qualified Control.Monad.State as State



data NWLState l = NWLState {
    lset :: HM.HashMap l [Int],
    -- derivable:: HM.HashMap l (HM.HashMap (l,Int) [(l, Int)]) }
    derivable :: HM.HashMap l (HM.HashMap (l, Int) [(l, Int)]) }
    deriving Show

instance HasLSet (NWLState l) l where
  getLSet = lset
  setLSet lset s = s { lset = lset }

class (Monad m, HasLSet wl l) => MonadNWL wl l m | m -> wl l where
    asNWL :: LV t l =>  m (t l a) -> m (t l a)
    getNWLState :: m wl
    putNWLState :: wl -> m ()
    modifyNWLState :: (wl -> wl) -> m ()


instance (Monad m, Hashable l, Eq l, HasLSet (NWLState l) l) => MonadNWL (NWLState l) l (StateT (NWLState l) m) where
    asNWL m = do
      lv <- m
      s <- getNWLState
      let ll = concatMap (\(k, v) -> map (k,) v) (HM.toList (lset s)) -- all the labels that are in the lset
      let derivl = HM.lookupDefault HM.empty (getLabel' lv) (derivable s) -- all the derivable labels for the current label
      let newDerivl = foldl' (\acc (l,i) -> HM.insertWith List.union (l,i) ll acc) derivl ll -- for each label in ll, add all the other labels to the derivable map
      putNWLState $ s {derivable = HM.insert (getLabel' lv) newDerivl (derivable s)}
      return lv
    getNWLState = State.get
    putNWLState = State.put
    modifyNWLState = State.modify

instance (MonadIFC st scurr rel l m, MonadNWL (NWLState l) l (StateT (NWLState l) m))
  => MonadIFC st scurr rel l (StateT (NWLState l) m) where
  label l a = guard l >> labelInternal l a
  labelInternal l a = lift $ labelInternal l a

  unlabel lv= do
    x               <- lift $ unlabel lv -- taint l i >> return a
    s               <- get
    wl@(NWLState _ derivable) <- getNWLState

    -- if the label l that we are unlabeling is a key of derivable then for all l' in lset that can be used to derive from l then we need to add all the derivable labels to lset
    let derivableFroml = HM.elems $ HM.filterWithKey (\k _ -> k == getLabel' lv) derivable
    let derivableFromlandLset = concatMap (concat . HM.elems . HM.filterWithKey (\k _ -> k `elem` concatMap (\(k', v) -> map (k',) v) (HM.toList (getLSet s)))) derivableFroml--HM.keys (getLSet s) )) derivableFroml
    let newLset = foldl' (\acc (lab, i) -> insert lab i acc ) (getLSet s) derivableFromlandLset


    -- if lset contains an l' that can be used to derive this with l then we need to add all the derivable labels to lset
    let derivableFromLset = HM.elems $ HM.filterWithKey (\k v -> k `elem` HM.keys newLset ) derivable
    let derivableFromLsetandl = concatMap (concat . HM.elems . HM.filterWithKey (\k _ -> k == (getLabel' lv, getId' lv) )) derivableFromLset
    let newLset' = foldl' (\acc (lab, i) -> insert lab i acc ) newLset derivableFromLsetandl

    -- putNWLState $ NWLState (getLSet s) derivable
    -- putNWLState $ setLSet newLset' wl
    lset <- getLSet <$> get
    let lset' = HM.unionWith List.union newLset' lset
    modifyNWLState $ modifyLSet (HM.unionWith List.union lset')

    return x

  guard l = do

    lc  <- getLSet <$> get
    -- for all derivable lv  create an lset containing only it -> getRelation -> check
    s <- get
    derivableFroml <- HM.elems . HM.filterWithKey (\k _ -> k == l) . derivable <$> getNWLState
    let derivableFromlandLset = concatMap (concat . HM.elems . HM.filterWithKey (\k _ -> k `elem` concatMap (\(k', v) -> map (k',) v) (HM.toList (getLSet s)))) derivableFroml--HM.keys lc )) derivableFroml 
    -- let newLset = Data.List.foldl' (\acc (lab, i) -> HM.insertWith (Data.List.union) lab [i] acc ) lc (concat $ HM.elems derivableFromliandLset)
    let newLset = foldl' (\acc (lab, i) -> insert lab i acc ) lc derivableFromlandLset
    put $ setLSet newLset s
    lift $ guard l
    put $ setLSet lc s



    -- let toCheck = concatMap (\(k, v) -> map (k,) v) (HM.toList lc) `intersect` (HM.keys derivablel)
    -- mapM_ (\k -> do
    --       -- s <- get
    --       let nwl = map (\(ll,i) -> (ll, [i])) $ HM.lookupDefault [] k derivablel -- get the derivable labels for the current label
    --       let newlset = HM.fromListWith (++) nwl -- create a new lset containing only the derivable labels
    --       put (setLSet newlset s) -- set the new lset 
    --       lift $ guard l
    --       -- fail ("guard " ++ show l ++ " failed")
    --       ) toCheck
    -- put $ setLSet lc s

  getRelation  lset= lift $ getRelation lset

  get    = lift get
  put  s  = do
    -- NWLState _ derivable <- getNWLState
    -- putNWLState $ NWLState (getLSet s) derivable
    lift $ put s

  modify s= do
    lift $ modify s
    -- lset <- getLSet <$> get
    -- NWLState _ derivable <- getNWLState
    -- putNWLState $ NWLState lset derivable

  setUserState news= do
    lset <- getLSet <$> getNWLState
    oldRel <- getRelation lset
    s      <- get
    put $ setScurr news s
    newRel <- getRelation lset
    when (any (incUpperSet (oldRel) (newRel)) $ HM.keys lset)
         (fail "incUpperClosure check failed")
    lift $ setUserState news

  resetOP = do
    rs <- lift resetOP
    s <- get
    return
      (do
        lift rs
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

  readIORef lv= do
    x               <- lift $ readIORef lv -- taint l i >> return a
    s               <- get
    wl@(NWLState _ derivable) <- getNWLState

    -- if the label l that we are unlabeling is a key of derivable then for all l' in lset that can be used to derive from l then we need to add all the derivable labels to lset
    let derivableFroml = HM.elems $ HM.filterWithKey (\k _ -> k == getLabel' lv) derivable
    let derivableFromlandLset = concatMap (concat . HM.elems . HM.filterWithKey (\k _ -> k `elem` concatMap (\(k', v) -> map (k',) v) (HM.toList (getLSet s)))) derivableFroml--HM.keys (getLSet s) )) derivableFroml
    let newLset = foldl' (\acc (lab, i) -> insert lab i acc ) (getLSet s) derivableFromlandLset


    -- if lset contains an l' that can be used to derive this with l then we need to add all the derivable labels to lset
    let derivableFromLset = HM.elems $ HM.filterWithKey (\k v -> k `elem` HM.keys newLset ) derivable
    let derivableFromLsetandl = concatMap (concat . HM.elems . HM.filterWithKey (\k _ -> k == (getLabel' lv, getId' lv) )) derivableFromLset
    let newLset' = foldl' (\acc (lab, i) -> insert lab i acc ) newLset derivableFromLsetandl

    -- putNWLState $ NWLState (getLSet s) derivable
    -- putNWLState $ setLSet newLset' wl
    lset <- getLSet <$> get
    let lset' = HM.unionWith List.union newLset' lset
    modifyNWLState $ modifyLSet (HM.unionWith List.union lset')
    return x
    
    

insert
  :: (Hashable k, Eq a, Eq k) => k -> a -> HM.HashMap k [a] -> HM.HashMap k [a]
insert k v m = case HM.lookup k m of
  Nothing -> HM.insert k [v] m
  Just xs -> HM.insert k (nub $ v : xs) m