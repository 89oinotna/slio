{-# LANGUAGE MultiParamTypeClasses, TupleSections #-}
module SimpleStLIO
       (SLIO(..), Labeled,  LIORef, Label(..), LIOState(..),
        label, unlabel, labelOf, relabel,
        getLabel, getState, setState,
        newLIORef, writeLIORef, readLIORef, labelOfRef,
        toLabeled, labelT)
where



import Control.Applicative


import Prelude hiding (fail)
import Control.Monad.Fail (MonadFail (..))

import Control.Monad hiding (guard)
import Data.List
import Data.IORef

import Debug.Trace (traceShow)

data LIOState l st = LIOState { lcurr :: [l], scurr :: st, tlab :: [l] }
  deriving (Show)

newtype SLIO l st a = SLIO { unSLIO :: LIOState l st -> IO (a, LIOState l st) }

instance Monad (SLIO l st) where
  return x = SLIO (\s -> return (x, s))
  SLIO f >>= g = SLIO $ \s ->
    do (x,s') <- f s
       unSLIO (g x) s'

instance MonadFail (SLIO l st) where
  fail err = SLIO (\_ -> fail err)

instance Functor (SLIO l st) where
  fmap = liftM

instance Applicative (SLIO l st) where
  pure = return
  (<*>) = ap

class (Eq l, Show l) => Label l st where
  -- check to ensure that l1 lis less restricrtive than l2 in s
  lrt :: st -> l -> l -> Bool
  incUpperSet :: st -> st -> l -> Bool


data Labeled l a = Lb l a | TLb l a
                 deriving (Eq, Show)

-- data TransientLabeled l a=TLb l a 
--                 deriving (Eq, Show)

data LIORef l a = LIORef l (IORef a)

lioError s = fail s

-- internal primitives

getLabel :: Label l st => SLIO l st [l]
getLabel = SLIO (\s -> return (lcurr s, s))

getState :: Label l st => SLIO l st st
getState = SLIO (\s -> return (scurr s, s))

setState :: Label l st => st -> SLIO l st ()
setState st = SLIO (\(LIOState lcurr scurr tlab) ->
                      do when (any (incUpperSet scurr st) lcurr) (lioError "incUpperClosure check failed")
                         return ((), LIOState lcurr st tlab))

taint :: Label l st => l -> SLIO l st ()
taint l = SLIO (\(LIOState lcurr scurr tlab) -> return ((), LIOState (nub (l : lcurr)) scurr tlab))

check scurr lcurr l = and [ lrt scurr x l | x <- lcurr ]

guard :: Label l st => l -> SLIO l st ()
guard l = do lcurr <- getLabel
             scurr <- getState
             let checkPassed = check scurr lcurr l
             unless checkPassed (lioError "label check failed")

io :: Label l st => IO a -> SLIO l st a
io m = SLIO (\s -> fmap (,s) m)

-- exported functions

label :: Label l st => l -> a -> SLIO l st (Labeled l a)
label l x = guard l >> return (Lb l x)

labelT :: Label l st => l -> a -> SLIO l st (Labeled l a)
labelT l x = guard l >> return (TLb l x)

unlabel :: Label l st => Labeled l a -> SLIO l st a
unlabel (Lb l x) = taint l >> return x
unlabel (TLb l x)= taint l >> taintT l >> return x

-- unlabelT :: Label l st => TransientLabeled l a -> SLIO l st a
-- unlabelT (TLb l x) = taint l >> taintT l >> return x

taintT :: Label l st => l -> SLIO l st ()
taintT l = SLIO (\(LIOState lcurr scurr tlab) -> return ((), LIOState lcurr scurr (nub (l : tlab))))

labelOf :: Labeled l a -> l
labelOf (Lb l x) = l
labelOf (TLb l x)=l

relabel :: Label l st => Labeled l a -> l -> SLIO l st (Labeled l a)
relabel lblVal lbl = toLabeled lbl (unlabel lblVal)

newLIORef :: Label l st => l -> a -> SLIO l st (LIORef l a)
newLIORef l x = do guard l
                   ref <- io $ newIORef x
                   return (LIORef l ref)

readLIORef :: Label l st => LIORef l a -> SLIO l st a
readLIORef (LIORef l ref) = do taint l
                               io (readIORef ref)

writeLIORef :: Label l st => LIORef l a -> a -> SLIO l st ()
writeLIORef (LIORef l ref) v = do guard l
                                  io (writeIORef ref v)

labelOfRef :: LIORef l a -> l
labelOfRef (LIORef l ref) = l

toLabeled :: Label l st => l -> SLIO l st a -> SLIO l st (Labeled l a)
toLabeled l m = SLIO (\s ->
                 let LIOState ll ss tt=  s in
                  traceShow ll $
                 do (x,LIOState lcurr scurr tlab) <- unSLIO m s
                    let checkPassed = traceShow ("lcurr:"++show lcurr) $ check scurr lcurr l
                    when (not checkPassed) (lioError "label check failed")
                    return (Lb l x, LIOState (nub tlab++ll) ss (nub tt++tlab)))