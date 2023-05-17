{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FunctionalDependencies #-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE InstanceSigs #-}
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
  , io
  )
    where



import Control.Monad.Trans.State.Strict


import           Control.Applicative
--import Data.Biapplicative

import           Control.Monad.Fail             ( MonadFail(..) )
import           Prelude                 hiding ( fail )

import Control.Monad (unless, when )
import Data.IORef ( newIORef, readIORef, writeIORef, IORef )
import Data.List ( nub )
-- import           Debug.Trace                    ( traceShow )
import qualified Data.List as List
import qualified Data.HashMap.Strict as HM
import Data.Hashable
import Control.Monad.Trans.Class  (lift)

-- the bool in rlab tracks the fact that a global unlabel has been done
-- the guard has to check that any info in the computation (unlabeled) can flow to the label 
-- we can replay information only if there wasnt any global unlabeling or if all of the replaying (all the ids from 0 to current) can flow to the label
data  LIOState l st r = LIOState
  { lcurr :: HM.HashMap l [Int]
  , scurr :: st
 -- NON TIME TRANSITIVE 
  , ntlab :: HM.HashMap l [Int]
  , assocnt :: HM.HashMap (l, Int) (HM.HashMap l [Int])
  , rlab  :: r
  , newid :: Int
  }--, ids :: Map String Int }
  deriving Show



--data FlowTo l = FlowTo l l
-- data R l l1 = Rep Int l l1
--   deriving (Eq, Show)

class (Show r, Label l st r) => Replaying r l st | r l -> st where
  addPromises :: l -> Int -> [l] -> SLIO l st r ()
  enableRP    :: l -> SLIO l st r ()
  disableRP   :: l -> Int -> SLIO l st r ()


class HasNTLab l st where
  getNTLab :: st -> HM.HashMap l [Int]
  setNTLab :: HM.HashMap l [Int] -> st -> st
  modifyNTLab :: (HM.HashMap l [Int] -> HM.HashMap l [Int]) -> st -> st
  modifyNTLab m st = setNTLab (m (getNTLab st)) st 
  
instance HasNTLab l (LIOState l st r) where
  getNTLab = ntlab
  setNTLab nt s = s { ntlab = nt }

type SLIO l st r a = StateT (LIOState l st r) IO a 

class (Eq l, Show l, Hashable l) => Label l st r where
  lrt :: st -> HM.HashMap l [Int] -> r -> l -> l -> Bool
  incUpperSet :: st -> st -> HM.HashMap l [Int] -> r -> r -> l -> Bool


data Labeled l a  = Lb { labelOf :: l, valueOf ::  a, idOf :: Int}
             deriving (Eq, Show)

data LIORef l a = LIORef {labelOfRef :: l, _lioRefVal :: IORef a, lioRefInt :: Int}


class LV t l where
  getLabel' :: t l a -> l
  getId'    :: t l a -> Int

instance LV LIORef l  where
  getLabel'  = labelOfRef
  getId'     = lioRefInt

instance LV Labeled l  where
  getLabel' = labelOf
  getId'    = idOf 

lioError :: MonadFail m => String -> m a
lioError s = fail s



-- internal primitives

getLabel :: (Replaying r l st, Label l st r) => SLIO l st r (HM.HashMap l [Int])
getLabel = lcurr <$> get

getState :: (Replaying r l st, Label l st r) => SLIO l st r st
getState = scurr <$> get


getAssocNT :: (Eq l, Hashable l, Monad m) => l -> Int -> StateT (LIOState l st r) m (HM.HashMap l [Int])
getAssocNT l i = HM.lookupDefault HM.empty (l,i) .  assocnt <$> get

getReplaying :: SLIO l st r r
getReplaying = rlab <$> get 


setState :: Label l st r => st -> SLIO l st r ()
setState st = do 
   s <- get 
   when (any (incUpperSet (scurr s) st (lcurr s) (rlab s) (rlab s)) $ HM.keys (lcurr s))
         (lioError "incUpperClosure check failed")
   put (s {scurr = st})


check :: Label l st r => st -> HM.HashMap l [Int] -> r -> l -> Bool
check sc lc rl l = and [ lrt sc lc rl x l | x <- HM.keys lc ]

guard :: (Replaying r l st, Label l st r) => l -> SLIO l st r ()
guard l = do
  lc <- getLabel
  sc <- getState
  rl  <- getReplaying
  let checkPassed = check sc lc rl l
  unless checkPassed (lioError "label check failed")

io :: Label l st r => IO a -> SLIO l st r a
io = lift 


addAssocNt :: Label l st r => l -> Int -> SLIO l st r ()
addAssocNt l i 
  = modify $ \s ->
              s {assocnt = HM.insertWith (HM.unionWith List.union) (l,i) (ntlab s) (assocnt s)}

label :: (Replaying r l st, Label l st r) => l -> a -> SLIO l st r (Labeled l a)
label l x = do
  guard l
  enableRP l
  i <- getNewId
  addAssocNt l i
  return (Lb l x i)

getNewId :: (Replaying r l st, Label l st r) => SLIO l st r Int
getNewId = do modify $ \s -> s { newid = newid s + 1}
              newid <$> get



-- TODO: set true in rlab
unlabel :: (Replaying r l st, Label l st r) => Labeled l a -> SLIO l st r a
unlabel (Lb l x i) = do 
    taint l i
    nt <- getAssocNT l i
    taintNT' nt
    taint' nt
    return x

asNT :: (Replaying r l st, Label l st r, LV t l) => (t l a -> SLIO l st r a) -> t l a -> SLIO l st r a
asNT f ld = do
  taintNT (getLabel' ld) (getId' ld)
  f ld

asRP :: (Replaying r l st, Label l st r, LV t l) => (t l a -> SLIO l st r a) ->[l] -> t l a-> SLIO l st r a
asRP f lst ld= do
  addPromises (getLabel' ld) (getId' ld) lst
  f ld

insert :: (Hashable k, Eq a, Eq k) => HM.HashMap k [a] -> k -> a -> HM.HashMap k [a]
insert m k v = case HM.lookup k m of
  Nothing -> HM.insert k [v] m
  Just xs -> HM.insert k (nub $ v:xs) m

taint :: (Replaying r l st, Label l st r) => l -> Int -> SLIO l st r ()
taint l i = modify $ \s -> s { lcurr = insert (lcurr s) l i}

taint' :: (Replaying r l st, Label l st r) => HM.HashMap l [Int] -> SLIO l st r ()
taint' ls = 
   modify $ \s -> s { lcurr = HM.unionWith List.union ls (lcurr s)}

taintNT :: (Replaying r l st, Label l st r) => l -> Int -> SLIO l st r ()
taintNT l i = 
  modify $ \s -> s { ntlab = insert (ntlab s) l i }





taintNT' :: (Monad m, HasNTLab l s, Eq l, Hashable l)
         => HM.HashMap l [Int] -> StateT s m ()
taintNT' nt = modify $ modifyNTLab (HM.unionWith List.union nt)

relabel :: (Replaying r l st, Label l st r)
        => Labeled l a
        -> l
        -> SLIO l st r (Labeled l a)
relabel lblVal lbl = toLabeled lbl (unlabel lblVal)

newLIORef :: (Replaying r l st, Label l st r) => l -> a -> SLIO l st r (LIORef l a)
newLIORef l x = 
  do
  guard l
  enableRP l
  ref <- io $ newIORef x
  i <- getNewId
  addAssocNt l i
  return (LIORef l ref i)

readLIORef :: (Replaying r l st, Label l st r) => LIORef l a -> SLIO l st r a
readLIORef (LIORef l ref i) = do
  taint l i 
  nt <- getAssocNT l i
  taintNT' nt
  taint' nt
  io (readIORef ref)

writeLIORef
  :: (Replaying r l st, Label l st r) => LIORef l a -> a -> SLIO l st r ()
writeLIORef (LIORef l ref i) v = do
  guard l
  enableRP l
  disableRP l i
  addAssocNt l i
  --enablePromises l
  io (writeIORef ref v)


-- what about replaying state in a toLabekled???
toLabeled :: Replaying r l st
          => l
          -> StateT (LIOState l st r) IO a
          -> StateT (LIOState l st r) IO (Labeled l a)
toLabeled l m = do 
  s1      <- get 
  (x, s2) <- lift (runStateT m s1)
  s3      <- lift (execStateT (enableRP l) s2)
  let checkPassed =  check (scurr s2) (lcurr s2) (rlab s2) l
  unless checkPassed (lioError "label check failed")
  put $ s1 { assocnt = HM.insertWith (HM.unionWith List.union) (l, (newid s2)) (ntlab s2) (assocnt s2)
           , rlab    = rlab s3
           , newid   = newid s2+1 }
  return $ Lb l x (newid s2)
