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
module Prova
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
  , LV(..),
  MonadSLIO(..),
    RPState(..),
  MonadRP(..),
  disableRP,
  enableRP,
  addPromises
  , check
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

import           Prelude                 hiding ( fail )

-- import           Debug.Trace                    ( traceShow )
import qualified Data.HashMap.Strict           as HM
import           Data.HashSet
import           Data.Hashable
import           Data.IORef                     ( IORef, newIORef, writeIORef, readIORef )
import Data.HashMap.Internal.Strict (HashMap)
import Data.List (nub)
import qualified Data.List as List

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

class HasLSet st l | st -> l where
  getLSet :: st -> HM.HashMap l [Int]
  setLSet :: HM.HashMap l [Int] -> st -> st
  modifyLSet :: (HM.HashMap l [Int] -> HM.HashMap l [Int]) -> st -> st
  modifyLSet m st = setLSet (m (getLSet st)) st

class HasLVIds st where
  getId :: st -> Int
  setId :: Int -> st -> st
  incId :: st -> st


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

class Relation rel l => ToRelation state rel l | state -> rel l  where
    toRelation :: state -> rel l

class -- (MonadState (st rel l) m, 
    -- (HasRelation st rel l, 
    (
    MutableRelation rel l, 
    -- HasLSet st l, HasLVIds st, 
    MonadFail m, MonadIO m
    )
    => MonadIFC rel l m | m -> rel l where

  label ::  l -> a -> m (Labeled l a)

  labelInternal :: l -> a -> m (Labeled l a)

  unlabel ::  Labeled l a -> m a

  guard ::  l -> m ()

  getRelation :: HashMap l [Int] -> m (rel l)

  toLabeled ::  l -> m a -> m (Labeled l a)

  resetOP :: m (m ())

  readIORef ::  LIORef l a -> m a

  writeIORef ::  LIORef l a -> a -> m ()

  newIORef ::  l -> a -> m (LIORef l a)

  newIORefInternal ::  l -> a -> m (LIORef l a)

  writeIORefInternal ::  LIORef l a -> a -> m ()

  getLSet' :: m (HM.HashMap l [Int])
  getLVId' :: m Int 
  putLSet' :: HM.HashMap l [Int] -> m ()
  putLVId' :: Int -> m ()
  -- User must not use those functions
  -- get :: m st
  -- put :: st -> m ()
  -- modify :: (st -> st) -> m ()


check :: (MutableRelation rel l, Relation rel l, MonadIFC  rel l m) 
    => HashMap l [Int] -> l -> m ()
check lset l = do
    rel <- getRelation lset
    let checkPassed = and [ lrt rel x l | x <- HM.keys lset ]
    unless checkPassed (fail "label check failed")

type Lset l = HM.HashMap l [Int]

data SLIOState scurr l = SLIOState
  { lset  :: Lset l
  , scurr :: scurr
  , newid :: Int
  }
  deriving Show

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



class (MutableRelation rel l, ToRelation scurr rel l, Monad m) => MonadSLIO scurr rel l m | m -> scurr rel l where
  getSLIOState :: m scurr
  putSLIOState :: scurr -> m ()
  modifySLIOState :: (scurr -> scurr) -> m ()

instance (MutableRelation rel l, ToRelation scurr rel l, 
    MonadIFC rel l (StateT st m), MonadIO m, MonadFail m, HasScurr st scurr, HasLSet st l, HasLVIds st) 
  => MonadSLIO scurr rel l (StateT st m) where
  getSLIOState = getScurr <$> State.get
  putSLIOState newState = do
    s <- State.get
    when
      ( any (incUpperSet (toRelation $ getScurr s) (toRelation newState))
      $ HM.keys (getLSet s)
      )
      (fail "incUpperClosure check failed")
    State.put $ setScurr newState s
  modifySLIOState f = do
    s <- State.get
    when
      ( any (incUpperSet (toRelation $ getScurr s) (toRelation $ f $ getScurr s))
      $ HM.keys (getLSet s)
      )
      (fail "incUpperClosure check failed")
    State.modify $ setScurr (f $ getScurr s)

instance (MonadIO io, MutableRelation rel l, HasLSet (SLIOState scurr l) l,
      HasScurr (SLIOState scurr l) scurr, ToRelation scurr rel l,
  HasLVIds (SLIOState scurr l),
  -- , MonadFail (StateT (SLIOState scurr l) io))
  MonadFail io
  )
  => MonadIFC  rel l (StateT (SLIOState scurr l) io) where
  label l a = guard l >> labelInternal l a
  labelInternal l a = incAndGetId >>= return . (Lb l a)
  unlabel (Lb l a i) = taint l i >> return a

  guard l = do
    lc  <- getLSet'
    check lc l

  getRelation lset= toRelation . getScurr <$> State.get

  -- get         = State.get
  -- put         = State.put
  -- modify      = State.modify
  getLSet' = getLSet <$> State.get
  getLVId' = getId <$> State.get
  putLSet' = State.modify . setLSet
  putLVId' = State.modify . setId 
  resetOP     = do
    ls <- getLSet'
    return
      (do
        -- ns <- get
        putLSet' ls
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
  :: (MonadIFC rel l m) => m Int
incAndGetId = do
  -- s <- get
  -- modify incId
  -- return $ getId s
  i <- getLVId'
  putLVId' (succ i)
  return i

taint
  :: (Eq l, Hashable l, MonadIFC  rel l m)
  => l
  -> Int
  -> m ()
taint l i = --modify $ modifyLSet (Prova.insert l i)
  do
    ls <- getLSet'
    putLSet' $ Prova.insert l i ls

insert
  :: (Hashable k, Eq a, Eq k) => k -> a -> HM.HashMap k [a] -> HM.HashMap k [a]
insert k v m = case HM.lookup k m of
  Nothing -> HM.insert k [v] m
  Just xs -> HM.insert k (nub $ v : xs) m


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
  -- getRPRelation :: HM.HashMap l [Int] -> m (rel l)

instance (MonadIFC  rel l (StateT (RPState l) m), Monad m,
      ToRelation (RPState l) rel l
      ) => MonadRP (RPState l) l rel (StateT (RPState l) m) where
  asRP f lst ld = do
    addPromises (getLabel' ld) (getId' ld) lst
    f ld
  getRPState    = State.get
  putRPState  s  = do
    ls <- getLSet'
    rel <- getRelation ls
    reprel <- toRelation <$> State.get
    let reprel' = toRelation s
    let rel' = Prova.union reprel rel
    let rel_new' = Prova.union reprel' rel
    when (any (incUpperSet rel' rel_new') $ HM.keys  ls)
      (fail "incUpperClosure check failed")

  modifyRPState = State.modify
  -- getRPRelation lset = do
  --   modifyRPState (\(RPState (_, rp)) -> RPState (lset, rp))
  --   news <- getRPState
  --   return $ toRelation news


instance (MonadIFC  rel l m, ToRelation (RPState l) rel l)
  => MonadIFC rel l (StateT (RPState l) m) where
  label l a = guard l >> labelInternal l a--guard l>> incAndGetId >>= return . (Lb l a)
  labelInternal l a = do
    x <- lift $ labelInternal l a
    enableRP l
    return x

  unlabel lv = do
    x               <- lift $ unlabel lv -- taint l i >> return a
    ls               <- getLSet'
    RPState (_, rp) <- State.get
    State.put $ RPState (ls, rp)
    return x

  guard l = do
    lc  <- getLSet' 
    rel <- getRelation lc
    let checkPassed = and [ lrt rel x l | x <- HM.keys lc ]
    unless checkPassed (fail "rp label check failed")

  getRelation lset= do
    rprel <- toRelation <$> State.get -- getRPRelation lset
    rel   <- lift $ getRelation lset
    return (Prova.union rprel  rel) -- getRel <$> (lift get)

  -- get = lift get
  -- put s = do
  --   -- RPState (_, rp) <- getRPState
  --   -- putRPState $ RPState (getLSet s, rp)
  --   lift $ put s
  -- modify s = do
  --   lift $ modify s
  getLSet' = lift getLSet'
  putLSet' = lift . putLSet'
  getLVId' = lift getLVId'
  putLVId' = lift . putLVId'

  resetOP = do
    rs <- lift resetOP
    return
      (do
        lift rs
        ls               <- getLSet'
        RPState (_, rp) <- State.get
        State.put $ RPState (ls, rp)
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
    x               <- lift $ Prova.readIORef lv -- taint l i >> return a
    ls               <- getLSet'
    RPState (_, rp) <- State.get
    State.put $ RPState (ls, rp)
    return x

insert2
  :: (Hashable k, Eq a, Eq k)
  => HM.HashMap k [a]
  -> k
  -> [a]
  -> HM.HashMap k [a]
insert2 m k v = case HM.lookup k m of
  Nothing -> HM.insert k v m
  Just xs -> HM.insert k (nub $ v ++ xs) m

addPromises :: (MonadRP (RPState l) l rel m, MonadIFC rel l m) => l -> Int -> [l] -> m ()
addPromises l i lst = do
  RPState (lset, rp) <- getRPState
  let genl = List.map (l, i, , False) lst
  let
    nrl = case HM.lookup l rp of
      Nothing -> insert2 rp l genl
      Just ls -> insert2
        rp
        l
        (List.filter (\(l1, ii, l2, _) -> (l1, ii, l2, True) `notElem` ls) genl)
  putRPState $ RPState (lset, nrl)

enableRP :: (MonadRP (RPState l) l rel m, MonadIFC rel l m) => l -> m ()
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


disableRP :: (MonadRP (RPState l) l rel m, MonadIFC rel l m) => l -> Int -> m ()
disableRP l i = do
  RPState (lset, rp) <- getRPState
  let newrl = HM.mapMaybe
            -- (\k lst -> Just (List.map (\v@(l1, i1, l2, b)-> if l1 == l && i == i1 then (l1,i1,l2, False) else v) lst))
        (Just . List.filter (\(l1, i1, _, _) -> l1 /= l && i /= i1))
        rp

    -- in  traceShow ("post" ++ show newrl)
  putRPState $ RPState (lset, newrl)

instance (MonadSLIO scurr rel l m, MonadRP rp l rel (StateT rp m), 
      MonadIFC rel l (StateT rp m)) 
  => MonadSLIO scurr rel l (StateT rp m) where
  getSLIOState = lift getSLIOState
  putSLIOState s= do
    ls <- getLSet'
    rel <- getRelation ls
    lift $ putSLIOState s
    reln <- getRelation ls
    when (any (incUpperSet rel reln) $ HM.keys ls)
      (fail "incUpperClosure check failed")
  modifySLIOState s = do
    ls <- getLSet'
    rel <- getRelation ls
    lift $ modifySLIOState s
    reln <- getRelation ls
    when (any (incUpperSet rel reln) $ HM.keys ls)
      (fail "incUpperClosure check failed")
