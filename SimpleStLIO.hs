{-# LANGUAGE MultiParamTypeClasses, TupleSections #-}
module SimpleStLIO
       (SLIO(..), Labeled, LIORef, Label(..), LIOState(..),
        label, unlabel, labelOf, relabel,
        getLabel, getState, setState,
        newLIORef, writeLIORef, readLIORef, labelOfRef,
        toLabeled)
where

import Control.Applicative
import Control.Monad hiding (guard)
import Data.List
import Data.IORef

data LIOState l st = LIOState { lcurr :: [l], scurr :: st }

data SLIO l st a = SLIO { unSLIO :: LIOState l st -> IO (a, LIOState l st) }

instance Monad (SLIO l st) where
  return x = SLIO (\s -> return (x, s))
  SLIO f >>= g = SLIO $ \s ->
    do (x,s') <- f s
       unSLIO (g x) s'
  fail err = SLIO (\_ -> fail err)

instance Functor (SLIO l st) where
  fmap = liftM

instance Applicative (SLIO l st) where
  pure = return
  (<*>) = ap

class Eq l => Label l st where
  lrt :: st -> l -> l -> Bool
  incUpperSet :: st -> st -> l -> Bool

data Labeled l a = Lb l a
                 deriving Eq

data LIORef l a = LIORef l (IORef a)

lioError s = fail s

-- internal primitives

getLabel :: Label l st => SLIO l st [l]
getLabel = SLIO (\s -> return (lcurr s, s))

getState :: Label l st => SLIO l st st
getState = SLIO (\s -> return (scurr s, s))

setState :: Label l st => st -> SLIO l st ()
setState st = SLIO (\(LIOState lcurr scurr) ->
                      do when (any (incUpperSet scurr st) lcurr) (lioError "incUpperClosure check failed")
                         return ((), LIOState lcurr st))

taint :: Label l st => l -> SLIO l st ()
taint l = SLIO (\(LIOState lcurr scurr) -> return ((), LIOState (nub (l : lcurr)) scurr))

check scurr lcurr l = and [ lrt scurr x l | x <- lcurr ]

guard :: Label l st => l -> SLIO l st ()
guard l = do lcurr <- getLabel
             scurr <- getState
             let checkPassed = check scurr lcurr l
             when (not checkPassed) (lioError "label check failed")
             return ()

io :: Label l st => IO a -> SLIO l st a
io m = SLIO (\s -> fmap (,s) m)

-- exported functions

label :: Label l st => l -> a -> SLIO l st (Labeled l a)
label l x = guard l >> return (Lb l x)

unlabel :: Label l st => Labeled l a -> SLIO l st a
unlabel (Lb l x) = taint l >> return x

labelOf :: Labeled l a -> l
labelOf (Lb l x) = l

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
                 do (x,LIOState lcurr scurr) <- unSLIO m s        
                    let checkPassed = check scurr lcurr l
                    when (not checkPassed) (lioError "label check failed")
                    return (Lb l x, s))
