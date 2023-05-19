{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TupleSections          #-}

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE PolyKinds              #-}

{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE InstanceSigs           #-}
module SimpleStLIO
  ( SLIO
  , Labeled
  , LIORef
  , Label(..)
  , LIOState(..)
  , Replaying(..)
  , label
  , unlabel
  , labelOf
  , relabel
  , getLabel
  , getState
  , setState
  , newLIORef
  , writeLIORef
  , readLIORef
  , labelOfRef
  , toLabeled
  , asNT
  , asRP
  ) where



-- import Control.Monad.Trans.State.Strict
import           Control.Monad.State.Class
import           Control.Monad.State.Strict
                                         hiding ( guard )

--import Data.Biapplicative
import           Control.Applicative
import           Control.Monad.IO.Class         ( MonadIO(..)
                                                , liftIO
                                                )

import           Control.Monad.Fail             ( MonadFail(..) )
import           Prelude                 hiding ( fail )

import           Control.Monad                  ( unless
                                                , when
                                                )
-- import           Debug.Trace                    ( traceShow )
import           Control.Monad.Trans            ( lift )
import qualified Data.HashMap.Strict           as HM
import           Data.Hashable
import           Data.IORef                     ( IORef
                                                , newIORef
                                                , readIORef
                                                , writeIORef
                                                )
import           Data.List                      ( nub )
import qualified Data.List                     as List

-- the bool in rlab tracks the fact that a global unlabel has been done
-- the guard has to check that any info in the computation (unlabeled) can flow to the label
-- we can replay information only if there wasnt any global unlabeling or if all of the replaying (all the ids from 0 to current) can flow to the label
data LIOState l rel r = LIOState
  { lset    :: HM.HashMap l [Int]
  , scurr   :: rel
-- NON TIME TRANSITIVE
  , ntlab   :: HM.HashMap l [Int]
  , assocnt :: HM.HashMap (l, Int) (HM.HashMap l [Int])
  , rlab    :: r
  , newid   :: Int
  }
  deriving Show


class (Show r, HasRLab st r) => Replaying st r l | st -> r where
  addPromises :: l -> Int -> [l] -> StateT st m ()
  enableRP    :: l -> StateT st m ()
  disableRP   :: l -> Int -> StateT st m ()

class HasRLab st r  | st -> r where
  getRLab :: st -> r
  setRLab :: r -> st -> st
  modifyRLab :: (r -> r) -> st -> st
  modifyRLab m st = setRLab (m (getRLab st)) st

instance HasRLab (LIOState l st r) r where
  getRLab = rlab
  setRLab rl s = s { rlab = rl }


class HasLSet l st | st -> l where
  getLSet :: st -> HM.HashMap l [Int]
  setLSet :: HM.HashMap l [Int] -> st -> st
  modifyLSet :: (HM.HashMap l [Int] -> HM.HashMap l [Int]) -> st -> st
  modifyLSet m st = setLSet (m (getLSet st)) st

instance HasLSet l (LIOState l st r) where
  getLSet = lset
  setLSet lc s = s { lset = lc }

class (Eq l, Hashable l) => HasNTLab l st | st -> l where
  getNTLab :: st -> HM.HashMap l [Int]
  setNTLab :: HM.HashMap l [Int] -> st -> st
  getNTAssoc :: st -> HM.HashMap (l, Int) (HM.HashMap l [Int])
  setNTAssoc :: HM.HashMap (l, Int) (HM.HashMap l [Int]) -> st -> st
  modifyNTLab :: (HM.HashMap l [Int] -> HM.HashMap l [Int]) -> st -> st
  modifyNTLab f st = setNTLab (f (getNTLab st)) st
  modifyNTAssoc :: (HM.HashMap (l, Int) (HM.HashMap l [Int]) -> HM.HashMap (l, Int) (HM.HashMap l [Int])) -> st -> st
  modifyNTAssoc f st = setNTAssoc (f (getNTAssoc st)) st

instance (Eq l, Hashable l) => HasNTLab l (LIOState l st r) where
  getNTLab = ntlab
  setNTLab nt s = s { ntlab = nt }
  getNTAssoc = assocnt
  setNTAssoc ass s = s { assocnt = ass }


class HasScCurr st rel | st -> rel where
  getScCurr :: st -> rel
  setScCurr :: rel -> st -> st
  modifyScCurr :: (rel -> rel) -> st -> st
  modifyScCurr m st = setScCurr (m (getScCurr st)) st

instance HasScCurr (LIOState l st r) st where
  getScCurr = scurr
  setScCurr sc s = s { scurr = sc }

class HasLVIds st where
  getId :: st -> Int
  setId :: Int -> st -> st
  incId :: st -> st

instance HasLVIds (LIOState l st r) where
  getId = newid
  setId i s= s { newid = i }
  incId s = s { newid = succ $ newid s }

type SLIO l st r io a = StateT (LIOState l st r) io a

class (Eq l, Show l, Hashable l) => Label l rel r where
  lrt :: rel -> HM.HashMap l [Int] -> r -> l -> l -> Bool-- rel -> l -> l -> Bool --
  incUpperSet :: rel -> rel -> HM.HashMap l [Int] -> r -> r -> l -> Bool


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

lioError :: MonadFail m => String -> m a
lioError s = fail s


-- internal primitives

getLabel :: (HasLSet l st, Monad io) => StateT st io (HM.HashMap l [Int])
getLabel = getLSet <$> get

getState :: (Monad io, HasScCurr st rel) => StateT st io rel
getState = getScCurr <$> get


getAssocNT
  :: (Eq l, Hashable l, Monad m, HasNTLab l st)
  => l
  -> Int
  -> StateT st m (HM.HashMap l [Int])
getAssocNT l i = HM.lookupDefault HM.empty (l, i) . getNTAssoc <$> get

getReplaying :: (Monad m, HasRLab st r) => StateT st m r
getReplaying = getRLab <$> get


setState
  :: (Label l rel r, MonadFail io, HasLSet l st, HasRLab st r, HasScCurr st rel)
  => rel
  -> StateT st io () 
setState st = do
  s <- get
  when
    ( any (incUpperSet (getScCurr s) st (getLSet s) (getRLab s) (getRLab s))
    $ HM.keys (getLSet s)
    )
    (lioError "incUpperClosure check failed")
  put $ setScCurr st s


check :: Label l rel r => rel -> HM.HashMap l [Int] -> r -> l -> Bool
check sc lc rl l = and [ lrt sc lc rl x l | x <- HM.keys lc ]


-- class (Label l rel r, MonadIO io, MonadFail io, HasLSet l st, HasRLab st r, HasScCurr st rel)  => Guardable l st io where

guard
  :: ( Label l rel r
     , MonadIO io
     , MonadFail io
     , HasRLab st r
     , HasScCurr st rel
     , HasLSet l st
     )
  => l
  -> StateT st io ()--r
guard l = do
  lc <- getLabel
  sc <- getState
  rl <- getReplaying
  let checkPassed = check sc lc rl l
  unless checkPassed (lioError "label check failed")
  -- return rl


addAssocNt :: (HasNTLab l st, Monad m) => l -> Int -> StateT st m ()
addAssocNt l i = modify $ \s -> modifyNTAssoc
  (HM.insertWith (HM.unionWith List.union) (l, i) (getNTLab s))
  s
  -- = modify $ \s ->
  --             s {assocnt = HM.insertWith (HM.unionWith List.union) (l,i) (ntlab s) (assocnt s)}

-- label :: (Replaying st r l, Label l st r) => l -> a -> SLIO l st r (Labeled l a)
label
  :: ( Label l rel r
     , Replaying st r l
     , MonadFail io
     , MonadIO io
     , HasNTLab l st
     , HasRLab st r
     , HasScCurr st rel
     , HasLSet l st
     , HasLVIds st
     )
  => l
  -> a
  -> StateT st io (Labeled l a)
      -- => l -> a -> StateT (LIOState l st r) io (Labeled l a)
label l x = do
  guard l -- :: StateT (LIOState l st r) io r
  enableRP l
  i <- incAndGetId
  addAssocNt l i
  return (Lb l x i)

incAndGetId :: (Monad m, HasLVIds st) => StateT st m Int
incAndGetId = do
  modify incId
  getId <$> get



-- TODO: set true in rlab
unlabel
  :: (Monad io, HasNTLab l st, HasLSet l st)
  => Labeled l a
  -> StateT st io a
unlabel (Lb l x i) = do
  taint l i
  nt <- getAssocNT l i
  taintNT' nt
  taint' nt
  return x

asNT
  :: (LV t l, Monad io, HasNTLab l st)
  => (t l a -> StateT st io a)
  -> t l a
  -> StateT st io a
asNT f ld = do
  taintNT (getLabel' ld) (getId' ld)
  f ld

asRP
  :: (Replaying st r l, Label l st r, LV t l, Monad io)
  => (t l a -> StateT st io a)
  -> [l]
  -> t l a
  -> StateT st io a
asRP f lst ld = do
  addPromises (getLabel' ld) (getId' ld) lst
  f ld

insert
  :: (Hashable k, Eq a, Eq k) => k -> a ->HM.HashMap k [a] -> HM.HashMap k [a]
insert k v m = case HM.lookup k m of
  Nothing -> HM.insert k [v] m
  Just xs -> HM.insert k (nub $ v : xs) m

taint :: (Eq l, Hashable l, Monad io, HasLSet l st) => l -> Int -> StateT st io ()
taint l i = modify $ modifyLSet (insert l i)
  -- modify $ \s -> s { lset = insert (lset s) l i }

taint' :: (Eq l, Hashable l, Monad io, HasLSet l st) => HM.HashMap l [Int] -> StateT st io ()
taint' ls = modify $ modifyLSet (HM.unionWith List.union ls)
  -- modify $ \s -> s { lset = HM.unionWith List.union ls (lset s) }

taintNT :: (Eq l, Hashable l, Monad io, HasNTLab l st) => l -> Int -> StateT st io ()
taintNT l i = modify $ modifyNTLab (insert l i)
  -- modify $ \s -> s { ntlab = insert (ntlab s) l i }





taintNT'
  :: (Monad m, HasNTLab l s, Eq l, Hashable l)
  => HM.HashMap l [Int]
  -> StateT s m ()
taintNT' nt = modify $ modifyNTLab (HM.unionWith List.union nt)

relabel
  :: (Label l rel r
     , Replaying st r l
     , MonadFail io
     , MonadIO io
     , HasNTLab l st
     , HasRLab st r
     , HasScCurr st rel
     , HasLSet l st
     , HasLVIds st)
  => Labeled l a
  -> l
  -> StateT st io (Labeled l a)
relabel lblVal lbl = toLabeled lbl (unlabel lblVal)

newLIORef
  :: ( Label l rel r
     , Replaying st r l
     , MonadFail io
     , MonadIO io
     , HasNTLab l st
     , HasRLab st r
     , HasScCurr st rel
     , HasLSet l st
     , HasLVIds st
     )
  => l
  -> a
  -> StateT st io (LIORef l a)
newLIORef l x = do
  guard l
  enableRP l
  ref <- liftIO $ newIORef x
  i   <- incAndGetId
  addAssocNt l i
  return (LIORef l ref i)

readLIORef
  :: (MonadFail io, MonadIO io, HasNTLab l st, HasLSet l st)
  => LIORef l a
  -> StateT st io a
readLIORef (LIORef l ref i) = do
  taint l i
  nt <- getAssocNT l i
  taintNT' nt
  taint' nt
  liftIO (readIORef ref)

writeLIORef
  :: ( Label l rel r
     , Replaying st r l
     , MonadFail io
     , MonadIO io
     , HasNTLab l st
     , HasRLab st r
     , HasScCurr st rel
     , HasLSet l st
     , HasLVIds st
     )
  => LIORef l a
  -> a
  -> StateT st io ()
writeLIORef (LIORef l ref i) v = do
  guard l
  enableRP l
  disableRP l i
  addAssocNt l i
  --enablePromises l
  liftIO (writeIORef ref v)


-- what about replaying state in a toLabekled???
toLabeled
  :: ( Label l rel r
     , Replaying st r l
     , MonadFail io
     , HasLSet l st
     , HasRLab st r
     , HasScCurr st rel
     , HasLVIds st
     , HasNTLab l st
     )
  => l
  -> StateT st io a
  -> StateT st io (Labeled l a)
toLabeled l m = do
  s1      <- get
  (x, s2) <- lift (runStateT m s1)
  s3      <- lift (execStateT (enableRP l) s2)
  let checkPassed = check (getScCurr s2) (getLSet s2) (getRLab s2) l
  unless checkPassed (lioError "label check failed")
  modify $ setId ((1 + getId s2))
  modify $ setRLab (getRLab s3)
  modify $ setNTAssoc
        (HM.insertWith (HM.unionWith List.union)
                       (l, (getId s2))
                       (getNTLab s2)
                       (getNTAssoc s2)
        )
  -- put $ s1 { assocnt = HM.insertWith (HM.unionWith List.union) (l, (newid s2)) (ntlab s2) (assocnt s2)
  --          , rlab    = rlab s3
  --          , newid   = newid s2+1 }
  return $ Lb l x (getId s2)
