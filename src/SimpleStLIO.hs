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
  ( SLIO(..)
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
  ,io
  )--, unlabelR)--, sfmap)
    where



import Control.Monad.Trans.State.Strict


import           Control.Applicative
--import Data.Biapplicative

import           Control.Monad.Fail             ( MonadFail(..) )
import           Prelude                 hiding ( fail )

import Control.Monad ( MonadFail(fail), ap, liftM, unless, when )
import Data.IORef ( newIORef, readIORef, writeIORef, IORef )
import Data.List ( nub )
import           Debug.Trace                    ( traceShow )
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

class (Show (r), Label l st r) => Replaying r l st | r l-> st where
  -- TODO : use id info
  -- getNewId ::  l -> SLIO l st r Int

  -- trackUnlabel :: l -> Int -> SLIO l st r ()

  addPromises :: l -> Int -> [l] -> SLIO l st r ()

  enableRP :: l -> SLIO l st r ()

  disableRP :: l -> Int -> SLIO l st r ()



type SLIO l st r a = StateT (LIOState l st r) IO a 

{- 
instance Monad (SLIO l st r) where
  return x = SLIO (\s -> return (x, s))
  SLIO f >>= g = SLIO $ \s -> do
    (x, s') <- f s
    unSLIO (g x) s'

instance MonadFail (SLIO l st r) where
  fail err = SLIO (\_ -> fail err)

instance Functor (SLIO l st r) where
  fmap = liftM

instance Applicative (SLIO l st r) where
  pure  = return
  (<*>) = ap

-} 

class (Eq l, Show l, Hashable l) => Label l st r where
  -- check to ensure that l1 lis less restricrtive than l2 in s
  lrt :: st -> HM.HashMap l [Int] -> r -> l -> l -> Bool

  -- to avoid to conditional allow a flow
  incUpperSet :: st -> st -> HM.HashMap l [Int] -> r -> r -> l -> Bool

--newtype LV l a = LV (Either (Labeled l a) (LIORef l a))

data Labeled l a  = Lb l a Int
             deriving (Eq, Show)

data LIORef l a = LIORef l (IORef a) Int


class LV t l where-- |tlv c-> v where
  --getValue' :: tlv l c -> v
  getLabel' :: t l a-> l
  getId' :: t l a-> Int

instance LV LIORef l  where
  --getValue' (LIORef l ior i) = ior
  getLabel' (LIORef l ior i) = l
  getId' (LIORef l ior i) = i

instance LV Labeled l  where
  --getValue' (Lb l a i) = a
  getLabel' (Lb l ior i) = l
  getId' (Lb l ior i) = i

lioError s = fail s



-- internal primitives

getLabel :: (Replaying r l st, Label l st r) => SLIO l st r (HM.HashMap l [Int])
getLabel = lcurr <$> get

getState :: (Replaying r l st, Label l st r) => SLIO l st r st
getState = scurr <$> get


getNT :: (Replaying r l st, Label l st r) => SLIO l st r (HM.HashMap l [Int])
getNT = ntlab <$> get 

getAssocNT l i = HM.lookupDefault HM.empty (l,i) .  assocnt <$> get

getReplaying :: SLIO l st r r
getReplaying = rlab <$> get 


setState :: Label l st r => st -> SLIO l st r ()
setState st = do 
   state <- get 
   when (any (incUpperSet (scurr state) st (lcurr state) (rlab state) (rlab state)) $ HM.keys (lcurr state))
         (lioError "incUpperClosure check failed")
   put (state {scurr = st})


check :: Label l st r => st -> HM.HashMap l [Int] -> r -> l -> Bool
check scurr lcurr rlab l = and [ lrt scurr lcurr rlab x l | x <- HM.keys lcurr ]

guard :: (Replaying r l st, Label l st r) => l -> SLIO l st r ()
guard l = do
  lcurr <- getLabel
  scurr <- getState
  rlab  <- getReplaying
  let checkPassed = check scurr lcurr rlab l
  unless checkPassed (lioError "label check failed")

io :: Label l st r => IO a -> SLIO l st r a
io = lift 


addAssocNt :: Label l st r => l -> Int -> SLIO l st r ()
addAssocNt l i 
  = modify $ \state ->
              state {assocnt = HM.insertWith (HM.unionWith List.union) (l,i) (ntlab state) (assocnt state)}

label :: (Replaying r l st, Label l st r) => l -> a -> SLIO l st r (Labeled l a)
label l x = do
  guard l
  enableRP l
  i <- getNewId
  addAssocNt l i
  return (Lb l x i)

getNewId :: (Replaying r l st, Label l st r) => SLIO l st r Int
getNewId = do modify $ \state -> state { newid = newid state + 1}
              newid <$> get



-- TODO: set true in rlab
unlabel :: (Replaying r l st, Label l st r) => Labeled l a -> SLIO l st r a
unlabel (Lb l x i) = do 
    taint l i
    nt <- getAssocNT l i
    taintNT' nt
    taint' nt
    return x

valueOf :: Labeled l a -> a
valueOf (Lb l x i) = x

asNT :: (Replaying r l st, Label l st r, LV t l) => (t l a-> SLIO l st r a) -> t l a-> SLIO l st r a
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
taint l i = modify $ \state -> state { lcurr = insert (lcurr state) l i}

taint' :: (Replaying r l st, Label l st r) => HM.HashMap l [Int] -> SLIO l st r ()
taint' ls = 
   modify $ \state -> state { lcurr = HM.unionWith List.union ls (lcurr state)}

taintNT :: (Replaying r l st, Label l st r) => l -> Int -> SLIO l st r ()
taintNT l i = 
  modify $ \s -> s { ntlab = insert (ntlab s) l i }


taintNT' :: (Replaying r l st, Label l st r) => HM.HashMap l [Int] -> SLIO l st r ()
taintNT' nt = 
  modify $ \s -> s { ntlab = HM.unionWith List.union nt (ntlab s)}

labelOf :: Labeled l a -> l
labelOf (Lb l x _) = l
-- labelOf (NTLb l x _) = l

idOf :: Labeled l a -> Int
idOf (Lb   l x i) = i
-- idOf (NTLb l x i) = i

relabel
  :: (Replaying r l st, Label l st r)
  => Labeled l a
  -> l
  -> SLIO l st r (Labeled l a)
relabel lblVal lbl = toLabeled lbl (unlabel lblVal)

newLIORef
  :: (Replaying r l st, Label l st r) => l -> a -> SLIO l st r (LIORef l a)
newLIORef l x = 
  do
  guard l
  enableRP l
  --enablePromises l
  nt <- getNT
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


labelOfRef :: LIORef l a -> l
labelOfRef (LIORef l ref i) = l

-- what about replaying state in a toLabekled???
toLabeled
  :: (Replaying r l st, Label l st r)
  => l
  -> SLIO l st r a
  -> SLIO l st r (Labeled l a)
toLabeled l m = do 
  s@(LIOState ll ss nt ant rr nid) <- get 
  (x, s'@(LIOState lcurr scurr nt' ant' rlab newid)) <- lift (runStateT m s)
  LIOState _ _ _ _ rlab' _ <- lift (execStateT (enableRP l) s')
  let checkPassed =  check scurr lcurr rlab l
  unless checkPassed (lioError "label check failed")
  put $ LIOState ll ss nt (HM.insertWith (HM.unionWith List.union) (l, newid) nt' ant') rlab' (newid+1)
  return $ Lb l x newid
