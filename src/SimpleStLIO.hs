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

-- the bool in rlab tracks the fact that a global unlabel has been done
-- the guard has to check that any info in the computation (unlabeled) can flow to the label 
-- we can replay information only if there wasnt any global unlabeling or if all of the replaying (all the ids from 0 to current) can flow to the label
data  LIOState l st r = LIOState
  { lcurr :: HM.HashMap l [Int]
  , scurr :: st
  , ntlab :: HM.HashMap l [Int]
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

  enablePromises :: l -> SLIO l st r ()



newtype SLIO l st r a= SLIO { unSLIO :: LIOState l st r  -> IO (a, LIOState l st r ) }

instance Monad (SLIO l st r) where
  return x = SLIO (\s -> return (x, s))
  SLIO f >>= g = SLIO $ \s -> do
    (x, s') <- f s
    unSLIO (g x) s'

instance   MonadFail (SLIO l st r) where
  fail err = SLIO (\_ -> fail err)

instance Functor (SLIO l st r) where
  fmap = liftM

instance Applicative (SLIO l st r) where
  pure  = return
  (<*>) = ap

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
getLabel = SLIO (\s -> return (lcurr s, s))

getState :: (Replaying r l st, Label l st r) => SLIO l st r st
getState = SLIO (\s -> return (scurr s, s))

getReplaying
  :: (Label l st r, Replaying r l st)
  => SLIO l st r r
getReplaying = SLIO (\s -> return (rlab s, s))

-- getReplaying ::  Label l st r => SLIO l st r (Map String (Int, [(,) Int l]))
-- getReplaying = SLIO (\s -> return (rlab ids s, s))

setState :: (Replaying r l st, Label l st r) => st -> SLIO l st r ()
setState st = SLIO
  (\(LIOState lcurr scurr ntlab rlab newid) -> do
    when (any (incUpperSet scurr st lcurr rlab rlab) $ HM.keys lcurr)
         (lioError "incUpperClosure check failed")
    return ((), LIOState lcurr st ntlab rlab newid)
  )


check :: (Label l st r) => st -> HM.HashMap l [Int] -> r -> l -> Bool
check scurr lcurr rlab l = and [ lrt scurr lcurr rlab x l | x <- HM.keys lcurr ]

guard :: (Replaying r l st, Label l st r) => l -> SLIO l st r ()
guard l = do
  lcurr <- getLabel
  scurr <- getState
  rlab  <- getReplaying
  let checkPassed = check scurr lcurr rlab l
  unless checkPassed (lioError "label check failed")

io :: Label l st r => IO a -> SLIO l st r a
io m = SLIO (\s -> fmap (, s) m)


-- Used to check if allowing the replay is causing an increaseUpperSet
checkAndRep ::(Replaying r l st, Label l st r) => l -> SLIO l st r ()
checkAndRep l=  SLIO (\s@(LIOState lcurr scurr ntlab rlab newid) -> do
    (_, LIOState _ _ _ rlab' _) <- unSLIO (enablePromises l) s
    when (any (incUpperSet scurr scurr lcurr rlab rlab') $ HM.keys lcurr)
         (lioError "incUpperClosure check failed")
    return ((), LIOState lcurr scurr ntlab rlab' newid)
  )

-- exported functions

label :: (Replaying r l st, Label l st r) => l -> a -> SLIO l st r (Labeled l a)
label l x = do
  guard l
  checkAndRep l
  Lb l x <$> getNewId

getNewId :: (Replaying r l st, Label l st r) => SLIO l st r Int
getNewId = SLIO
  (\(LIOState lcurr scurr ntlab rlab newid) ->
          return
            ( newid
            --, LIOState lcurr scurr ntlab $ HM.insert k (n + 1, b, l) rlab
            , LIOState lcurr scurr ntlab rlab $ newid + 1
            )
  )


-- TODO: set true in rlab
unlabel :: (Replaying r l st, Label l st r) => Labeled l a -> SLIO l st r a
unlabel (Lb   l x i) =  taint l i>> return x

valueOf :: Labeled l a -> a
valueOf (Lb   l x i) = x

--type ASFUN l st r a= Either (Labeled l a  -> SLIO l st r a) (LIORef l a  -> SLIO l st r a)

-- instance Biapplicative Either where
--   (<<*>>) (Left f) (Left lv) = Left $ f lv
--   (<<*>>) (Right f) (Right lv) = Right $ f lv

-- prova :: (Replaying r l st, Label l st r, SS c d l a) => (c l a -> SLIO l st r a) -> c l a-> SLIO l st r a
-- prova f ld = do
--   taintNT (getLabel' ld) (getId' ld)
--   f ld
asNT :: (Replaying r l st, Label l st r, LV t l) => (t l a-> SLIO l st r a) -> t l a-> SLIO l st r a
asNT f ld = do
  taintNT (getLabel' ld) (getId' ld)
  f ld

asRP :: (Replaying r l st, Label l st r, LV t l) => (t l a -> SLIO l st r a) ->[l] -> t l a-> SLIO l st r a
asRP f lst ld= do
  addPromises (getLabel' ld) (getId' ld) lst
  f ld

-- NOTE: non transitive values are managed by adding their label to lcurr (coming from toLabeled)
-- asNT :: (Replaying r l st, Label l st r) => ASFUN l st r a -> Either (Labeled l a) (LIORef l a) -> SLIO l st r a
-- asNT f ld@(Left ((Lb l a i))) = do
--   taintNT l i
--   either id id (f <<*>> ld) 
-- asNT f ld@(Right ((LIORef l a i))) = do
--   taintNT l i
--   either id id (f <<*>> ld) 

-- asRP :: (Replaying r l st, Label l st r) => ASFUN l st r a-> [l] -> Either (Labeled l a) (LIORef l a) -> SLIO l st r a
-- asRP f lst ld@(Left ((Lb l a i)))= do
--   addPromises l i lst
--   either id id (f <<*>> ld) 
-- asRP f lst ld@(Right ((LIORef l a i)))= do
--   addPromises l i lst
--   either id id (f <<*>> ld) 


insert :: (Hashable k, Eq a, Eq k) => HM.HashMap k [a] -> k -> a -> HM.HashMap k [a]
insert m k v = case HM.lookup k m of
  Nothing -> HM.insert k [v] m
  Just xs -> HM.insert k (nub $ v:xs) m

taint :: (Replaying r l st, Label l st r) => l -> Int -> SLIO l st r ()
taint l i= SLIO
  (\(LIOState lcurr scurr ntlab rlab newid) ->
    return ((), LIOState (insert lcurr l i) scurr ntlab rlab newid)
  )

taintNT :: (Replaying r l st, Label l st r) => l -> Int -> SLIO l st r ()
taintNT l i= SLIO
  (\(LIOState lcurr scurr ntlab rlab newid) ->
    return ((), LIOState lcurr scurr (insert ntlab l i) rlab newid)
  )

labelOf :: Labeled l a -> l
labelOf (Lb   l x _) = l
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
  checkAndRep l
  --enablePromises l
  ref <- io $ newIORef x
  LIORef l ref <$> getNewId

readLIORef :: (Replaying r l st, Label l st r) => LIORef l a -> SLIO l st r a
readLIORef (LIORef l ref i) = do
  taint l i
  io (readIORef ref)

writeLIORef
  :: (Replaying r l st, Label l st r) => LIORef l a -> a -> SLIO l st r ()
writeLIORef (LIORef l ref i) v = do
  guard l
  checkAndRep l
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
toLabeled l m = 
      SLIO
        (\s@(LIOState ll ss tt rr nid) ->traceShow ll $ do
              (x, LIOState lcurr scurr ntlab rlab newid) <- unSLIO m s
              let checkPassed = traceShow ("lcurr:" ++ show lcurr)
                    -- $ check scurr lcurr rr l
                    $ check scurr lcurr rlab l
              unless checkPassed (lioError "label check failed")
              let news = LIOState (HM.unionWith List.union ntlab ll) ss (HM.unionWith List.union tt ntlab) rlab (newid+1)
              (_, LIOState lcurr' _ _ rlab' _) <- unSLIO (enablePromises l) news
              when (any (incUpperSet ss ss lcurr' rr rlab') $ HM.keys lcurr')
                (lioError "incUpperClosure check failed")
              return (Lb l x newid, news)
              --return (Lb l x nid, LIOState (HM.unionWith List.union ntlab ll) ss (HM.unionWith List.union tt ntlab) rr (nid+1))
        )
      --checkAndRep l
      --return x
    -- >>= label l --(\x -> do
        --  Lb l x <$> getNewId
        --)
