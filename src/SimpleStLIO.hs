{-# LANGUAGE MultiParamTypeClasses, TupleSections #-}
{-# LANGUAGE FunctionalDependencies #-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
module SimpleStLIO
       (SLIO(..), Labeled,  LIORef, Label(..), LIOState(..), FlowTo(..), Diff(..),
        label, unlabel, labelOf, relabel,
        getLabel, getState, setState,
        newLIORef, writeLIORef, readLIORef, labelOfRef,
        toLabeled, labelNT)--, sfmap)
where



import Control.Applicative


import Prelude hiding (fail)
import Control.Monad.Fail (MonadFail (..))

import Control.Monad hiding (guard)
import Data.List
import Data.IORef
import Debug.Trace (traceShow)

-- rlab should contain the flow from a replaying label to any label in lcurr (when it was unlabeled)
data FlowTo f l => LIOState l st f= LIOState { lcurr :: [l], scurr :: st, ntlab :: [l], rlab :: [f l] }
  deriving (Show)

--data FlowTo l = FlowTo l l

class (Eq (f l), Eq l) => FlowTo f l where
  source :: f l -> l
  target :: f l -> l

class (Eq a, Foldable res) => Diff st res a where
  difference :: st a-> st a-> res a

--instance FlowTo f a => Diff [] [] (f a) where
  --difference l1 l2= l1 \\ l2

newtype FlowTo f l => SLIO l st f a= SLIO { unSLIO :: LIOState l st f -> IO (a, LIOState l st f) }

instance(FlowTo f l) => Monad (SLIO l st f) where
  return x = SLIO (\s -> return (x, s))
  SLIO f >>= g = SLIO $ \s ->
    do (x,s') <- f s
       unSLIO (g x) s'

instance  (FlowTo f l) => MonadFail (SLIO l st f) where
  fail err = SLIO (\_ -> fail err)

instance(FlowTo f l) => Functor (SLIO l st f) where
  fmap = liftM

instance(FlowTo f l) => Applicative (SLIO l st f) where
  pure = return
  (<*>) = ap

class (Eq l, Show l) => Label l st where
  -- check to ensure that l1 lis less restricrtive than l2 in s
  lrt :: st -> l -> l -> Bool
  incUpperSet :: st -> st -> l -> Bool


-- | Labeling expressions of type @a@ with label @l@.
--newtype Lb l a = Lb {unLb :: a}

data Labeled l a  = Lb l a | NTLb l a| RLb l a | Empty a 
             deriving (Eq, Show)

pure :: a -> Labeled l a 
pure = Empty 
-- -- | Labeled resources as functors
-- sfmap :: (Eq l) => (a -> b) -> Labeled l a -> Labeled l b
-- sfmap f (Lb l a)= (<<*>>) (Lb l f) (Lb l a)
-- sfmap f (NTLb l a)= (<<*>>) (NTLb l f) (NTLb l a)
-- sfmap f (RLb l a)= (<<*>>) (RLb l f) (RLb l a)

-- -- Applicative operator (no pure)
-- (<<*>>)   :: (Eq l) => Labeled l (a -> b) -> Labeled l a -> Labeled l b
-- (Lb l f) <<*>> (Lb l' x) 
--   | l==l' = Lb l $ f x
-- (NTLb l f) <<*>> (NTLb l' x) 
--   | l==l' = NTLb l $ f x
-- (RLb l f) <<*>> (RLb l' x) 
--   | l==l' = RLb l $ f x

-- data TransientLabeled l a=TLb l a 
--                 deriving (Eq, Show)

data LIORef l a = LIORef l (IORef a)

lioError s = fail s

-- internal primitives

getLabel :: (Label l st, FlowTo f l) => SLIO l st f [l]
getLabel = SLIO (\s -> return (lcurr s, s))

getState ::  (Label l st, FlowTo f l)=> SLIO l st f st
getState = SLIO (\s -> return (scurr s, s))

setState ::  (Label l st, FlowTo f l) => st -> SLIO l st f ()
setState st = SLIO (\(LIOState lcurr scurr ntlab rlab) ->
                      do when (any (incUpperSet scurr st) lcurr) (lioError "incUpperClosure check failed")
                         when (checkReplaying scurr rlab st) (lioError "state update inconsistent with replaying information")
                         return ((), LIOState lcurr st ntlab rlab))

checkReplaying :: (FlowTo f l, Diff st res (f l)) => st a -> [a] -> st a -> Bool
checkReplaying scurr rlab st= any (`elem` rlab) $ difference scurr st

taint ::  (Label l st, FlowTo f l) => l -> SLIO l st f ()
taint l = SLIO (\(LIOState lcurr scurr ntlab rlab) -> return ((), LIOState (nub (l : lcurr)) scurr ntlab rlab))

check scurr lcurr l = and [ lrt scurr x l | x <- lcurr ]


guard ::  (Label l st, FlowTo f l) => l -> SLIO l st f ()
guard l = do lcurr <- getLabel
             scurr <- getState
             let checkPassed = check scurr lcurr l
             unless checkPassed (lioError "label check failed")

io ::  (Label l st, FlowTo f l) => IO a -> SLIO l st f a
io m = SLIO (\s -> fmap (,s) m)

-- exported functions

label ::  (Label l st, FlowTo f l) => l -> a -> SLIO l st f (Labeled l a)
label l x = guard l >> return (Lb l x)

labelNT ::  (Label l st, FlowTo f l) => l -> a -> SLIO l st f (Labeled l a)
labelNT l x = guard l >> return (NTLb l x)

unlabel ::  (Label l st, FlowTo f l) => Labeled l a -> SLIO l st f a
unlabel (Lb l x) = taint l >> return x
unlabel (NTLb l x)= taint l >> taintNT l >> return x
--unlabel (RLb l x) = taint l >> taintR l >> return x

-- unlabelT :: Label l st => TransientLabeled l a -> SLIO l st a
-- unlabelT (TLb l x) = taint l >> taintT l >> return x



--taintR :: Label l st => l -> SLIO l st f ()
--taintR l = SLIO (\(LIOState lcurr scurr ntlab rlab) -> return ((), LIOState lcurr scurr ntlab (nub (l : rlab))))

taintNT ::  (Label l st, FlowTo f l) => l -> SLIO l st f ()
taintNT l = SLIO (\(LIOState lcurr scurr ntlab rlab) -> return ((), LIOState lcurr scurr (nub (l : ntlab)) rlab))

labelOf :: Labeled l a -> l
labelOf (Lb l x) = l
labelOf (NTLb l x)=l

relabel ::  (Label l st, FlowTo f l) => Labeled l a -> l -> SLIO l st f (Labeled l a)
relabel lblVal lbl = toLabeled lbl (unlabel lblVal)

newLIORef ::  (Label l st, FlowTo f l) => l -> a -> SLIO l st f (LIORef l a)
newLIORef l x = do guard l
                   ref <- io $ newIORef x
                   return (LIORef l ref)

readLIORef ::  (Label l st, FlowTo f l) => LIORef l a -> SLIO l st f a
readLIORef (LIORef l ref) = do taint l
                               io (readIORef ref)

writeLIORef ::  (Label l st, FlowTo f l) => LIORef l a -> a -> SLIO l st f ()
writeLIORef (LIORef l ref) v = do guard l
                                  io (writeIORef ref v)

labelOfRef :: LIORef l a -> l
labelOfRef (LIORef l ref) = l

toLabeled ::  (Label l st, FlowTo f l) => l -> SLIO l st f a -> SLIO l st f (Labeled l a)
toLabeled l m = SLIO (\s ->
                 let LIOState ll ss tt pp=  s in
                  traceShow ll $
                 do (x,LIOState lcurr scurr ntlab rlab) <- unSLIO m s
                    let checkPassed = traceShow ("lcurr:"++show lcurr) $ check scurr lcurr l
                    when (not checkPassed) (lioError "label check failed")
                    return (Lb l x, LIOState (nub ntlab++ll) ss (nub tt++ntlab) rlab))