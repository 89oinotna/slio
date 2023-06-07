{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TupleSections          #-}

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE PolyKinds              #-}

{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE UndecidableInstances   #-}
module RP (
  RPState(..),
  MonadRP(..),
  disableRP,
  enableRP,
  addPromises 
) where



import qualified Control.Monad.State.Class     as State
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
import           Data.List                      ( nub )
import qualified Data.List                     as List
import           IFC

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
--   modifyRP m st = setRP (m (getRP st)) st

-- instance HasRP (RPState r l) r l where
--   getRP = rp
--   setRP rl s = s { rp = rl }

newtype RPState l = RPState {r::(HM.HashMap l [Int], HM.HashMap l [(l, Int, l, Bool)]) }
    deriving Show




class (Monad m, ToRelation rp rel l) => MonadRP rp l rel m | m -> rp l where
  asRP :: LV t l
    => (t l a -> m a)
    -> [l]
    -> t l a
    -> m a
  getRPState :: m rp
  putRPState :: rp -> m ()
  modifyRPState :: (rp -> rp) -> m ()
  getRPRelation :: m (rel l)

instance (Monad m, ToRelation (RPState l) rel l) => MonadRP (RPState l)  l rel (StateT (RPState l) m) where
  asRP f lst ld = do
    addPromises (getLabel' ld) (getId' ld) lst
    f ld
  getRPState    = State.get
  putRPState    = State.put
  modifyRPState = State.modify
  getRPRelation = toRelation <$> State.get

instance (MonadIFC st scurr rel l m, MonadRP (RPState l) l rel (StateT (RPState l) m))
  => MonadIFC st scurr rel l (StateT (RPState l) m) where
  label l a = guard l >> labelInternal l a--guard l>> incAndGetId >>= return . (Lb l a)
  labelInternal l a = do
    x <- lift $ labelInternal l a
    enableRP l
    return x

  unlabel lv = do
    x               <- lift $ unlabel lv -- taint l i >> return a
    s               <- get
    RPState (_, rp) <- getRPState
    putRPState $ RPState (getLSet s, rp)
    return x

  guard l = do
    lc  <- getLSet <$> get
    rel <- getRelation
    let checkPassed = and [ lrt rel x l | x <- HM.keys lc ]
    unless checkPassed (fail "rp label check failed")


  getRelation = do
    rprel <- getRPRelation
    rel   <- lift getRelation
    return (rprel `union` rel) -- getRel <$> (lift get)

  get = lift get
  put s = do
    RPState (_, rp) <- getRPState
    putRPState $ RPState (getLSet s, rp)
    lift $ put s
  modify s = do
    lift $ modify s
    lset            <- getLSet <$> get
    RPState (_, rp) <- getRPState
    putRPState $ RPState (lset, rp)
  setUserState scurr = do
    oldRel <- getRelation
    s      <- get
    put $ setScurr scurr s
    newRel <- getRelation
    when (any (incUpperSet (oldRel) (newRel)) $ HM.keys (getLSet s))
         (fail "incUpperClosure check failed")
  resetOP = do
    rs <- lift resetOP
    return
      (do
        lift rs
        s               <- get
        RPState (_, rp) <- getRPState
        putRPState $ RPState (getLSet s, rp)
      )
  toLabeled l m = do
    rop <- resetOP
    x   <- m
    lv  <- label l x
    rop
    return lv

  newIORefInternal l a =  do
    x <- lift $ newIORefInternal l a
    enableRP l
    return x

  newIORef l a = guard l >> newIORefInternal l a
  
  writeIORefInternal lv@(LIORef l a i) b = do
    x <- lift $ writeIORefInternal lv b
    disableRP l i
    return x

  writeIORef lv b = do
    guard (getLabel' lv)
    writeIORefInternal lv b
  
  readIORef lv = do
    x               <- lift $ readIORef lv -- taint l i >> return a
    s               <- get
    RPState (_, rp) <- getRPState
    putRPState $ RPState (getLSet s, rp)
    return x



insert
  :: (Hashable k, Eq a, Eq k)
  => HM.HashMap k [a]
  -> k
  -> [a]
  -> HM.HashMap k [a]
insert m k v = case HM.lookup k m of
  Nothing -> HM.insert k v m
  Just xs -> HM.insert k (nub $ v ++ xs) m


addPromises :: MonadRP (RPState l) l rel m => l -> Int -> [l] -> m ()
addPromises l i lst = do
  RPState (lset, rp) <- getRPState
  let genl = List.map (l, i, , False) lst
  let
    nrl = case HM.lookup l rp of
      Nothing -> insert rp l genl
      Just ls -> insert
        rp
        l
        (List.filter (\(l1, ii, l2, _) -> (l1, ii, l2, True) `notElem` ls) genl)
  putRPState $ RPState (lset, nrl)

enableRP :: MonadRP (RPState l) l rel m => l -> m ()
enableRP l = do
  RPState (lset, rp) <- getRPState
  let ls = HM.keys lset
  let nrl = HM.mapMaybe
        (Just . List.map
          (\v@(l1, i, l2, _) ->
            if l2 == l && l1 `elem` ls then (l1, i, l2, True) else v
          )
        )
        rp
      -- in  traceShow ("post" ++ show nrl)
  --put (LIOState lcurr st nt assocnt (Rep nrl) id)
  putRPState $ RPState (lset, nrl)


disableRP :: MonadRP (RPState l) l rel m => l -> Int -> m ()
disableRP l i = do
  RPState (lset, rp) <- getRPState
  let newrl = HM.mapMaybe
            -- (\k lst -> Just (List.map (\v@(l1, i1, l2, b)-> if l1 == l && i == i1 then (l1,i1,l2, False) else v) lst))
        (Just . List.filter (\(l1, i1, _, _) -> l1 /= l && i /= i1))
        rp

    -- in  traceShow ("post" ++ show newrl)
  putRPState $ RPState (lset, newrl)

