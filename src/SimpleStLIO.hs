{-# LANGUAGE MultiParamTypeClasses, TupleSections #-}
{-# LANGUAGE FunctionalDependencies #-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
module SimpleStLIO
       (SLIO(..), Labeled,  LIORef, Label(..), LIOState(..), FlowTo(..),
        label, unlabel, labelOf, relabel,
        getLabel, getState, setState,
        newLIORef, writeLIORef, readLIORef, labelOfRef,
        toLabeled, labelNT, unlabelR)--, sfmap)
where



import Control.Applicative


import Prelude hiding (fail)
import Control.Monad.Fail (MonadFail (..))

import Control.Monad hiding (guard)
import Data.List
import Data.IORef
import Debug.Trace (traceShow)
import Data.Map (Map, lookup, insert)
import Data.Maybe (Maybe)

-- rlab should contain the flow from a replaying label to any label in lcurr (when it was unlabeled)
data  LIOState l st f= LIOState { lcurr :: [l], scurr :: st, ntlab :: [l], rlab :: Map String (Int ,[(,) Int l]) }
  deriving (Show)

--data FlowTo l = FlowTo l l

class (Eq (f l), Eq l) => FlowTo f l where
  source :: f l -> l
  target :: f l -> l

--instance FlowTo f a => Diff [] [] (f a) where
  --difference l1 l2= l1 \\ l2

newtype  SLIO l st f a= SLIO { unSLIO :: LIOState l st f -> IO (a, LIOState l st f) }

instance Monad (SLIO l st f) where
  return x = SLIO (\s -> return (x, s))
  SLIO f >>= g = SLIO $ \s ->
    do (x,s') <- f s
       unSLIO (g x) s'

instance   MonadFail (SLIO l st f) where
  fail err = SLIO (\_ -> fail err)

instance Functor (SLIO l st f) where
  fmap = liftM

instance Applicative (SLIO l st f) where
  pure = return
  (<*>) = ap

class (Eq l, Show l) => Label l st where
  -- check to ensure that l1 lis less restricrtive than l2 in s
  lrt :: st -> l -> l -> Bool
  -- to avoid to conditional allow a flow
  incUpperSet :: st -> st -> l -> Bool

data Labeled l a  = Lb l a | NTLb l a| RLb l a Int
             deriving (Eq, Show)


data LIORef l a = LIORef l (IORef a)

lioError s = fail s

-- internal primitives

getLabel :: Label l st => SLIO l st f [l]
getLabel = SLIO (\s -> return (lcurr s, s))

getState ::  Label l st => SLIO l st f st
getState = SLIO (\s -> return (scurr s, s))

getReplaying ::  Label l st => SLIO l st f (Map String (Int, [(,) Int l]))
getReplaying = SLIO (\s -> return (rlab s, s))

setState ::  Label l st => st -> SLIO l st f ()
setState st = SLIO (\(LIOState lcurr scurr ntlab rlab) ->
                      do when (any (incUpperSet scurr st) lcurr) (lioError "incUpperClosure check failed")
                         return ((), LIOState lcurr st ntlab rlab))



check scurr lcurr l = and [ lrt scurr x l | x <- lcurr ]

guard ::  Label l st => l -> SLIO l st f ()
guard l = do lcurr <- getLabel
             scurr <- getState
             let checkPassed = check scurr lcurr l
             unless checkPassed (lioError "label check failed")

io ::  Label l st => IO a -> SLIO l st f a
io m = SLIO (\s -> fmap (,s) m)

-- exported functions

label ::  Label l st => l -> a -> SLIO l st f (Labeled l a)
label l x = guard l >> return (Lb l x)

labelNT ::  Label l st => l -> a -> SLIO l st f (Labeled l a)
labelNT l x = guard l >> return (NTLb l x)

labelR :: (FlowTo f l, Label l st) => l -> a -> SLIO l st f (Labeled l a)
labelR l x= do
              guard l
              i <- createLabel l
              return (RLb l x i)

createLabel :: (FlowTo f l, Label l st) => l -> SLIO l st f Int
createLabel l= SLIO (\(LIOState lcurr scurr ntlab rlab) ->
  let insert n lst=Data.Map.insert (show l) (n,lst) rlab
    in
  case Data.Map.lookup (show l) (rlab) of
    Just (n, lst) -> let nrlab = insert (n+1) lst in return (n + 1 , LIOState lcurr scurr ntlab nrlab)
    Nothing -> let nrlab = insert 1 [] in return (1 , LIOState lcurr scurr ntlab  nrlab)
  )
    --createFlows l lcurr = [ (l, ll) | ll <- lcurr]
    --insert n [] lcurr=Data.Map.insert (show l) (n,createFlows (n) lcurr) 
    --insert n lst lcurr=Data.Map.insert (show l) (n, lst ++ createFlows (n) lcurr)

unlabel ::  Label l st => Labeled l a -> SLIO l st f a
unlabel (Lb l x) = taint l >> return x
unlabel (NTLb l x)= taint l >> taintNT l >> return x

unlabelR :: (FlowTo f l, Show l) => Labeled l b -> [l] -> SLIO l st f b
--unlabelR (Lb l x) rsinks= taintR l rsinks >> return x -- not tainting lcurr (but in the guard for label then one needs to check also in rlab)
unlabelR (NTLb l x) rsinks= taintR l rsinks >> return x -- not tainting lcurr (but in the guard for label then one needs to check also in rlab)
unlabelR (Lb l x) rsinks= taintR l rsinks >> return x -- not tainting lcurr (but in the guard for label then one needs to check also in rlab)

taint ::  Label l st => l -> SLIO l st f ()
taint l = SLIO (\(LIOState lcurr scurr ntlab rlab) -> return ((), LIOState (nub (l : lcurr)) scurr ntlab rlab))

taintNT ::  Label l st => l -> SLIO l st f ()
taintNT l = SLIO (\(LIOState lcurr scurr ntlab rlab) -> return ((), LIOState lcurr scurr (nub (l : ntlab)) rlab))

taintR :: (FlowTo f l, Show l) => l -> [l] -> SLIO l st f (Map String (Int, [(Int, l)]))
taintR l rsinks= SLIO (\(LIOState lcurr scurr ntlab rlab) ->
  let insert n lst=Data.Map.insert (show l) (n,lst) rlab
      createFlows l = [ (l, ll) | ll <- rsinks]
    in
       case Data.Map.lookup (show l) (rlab) of
        Just (n, lst) -> let nrlab = (insert n $ nub lst++createFlows n) in return (nrlab , LIOState lcurr scurr ntlab nrlab)
      --Nothing -> let nrlab = (insert 1 $ createFlows 1) in return (1 , LIOState lcurr scurr ntlab  nrlab)
  )

-- unlabelT :: Label l st => TransientLabeled l a -> SLIO l st a
-- unlabelT (TLb l x) = taint l >> taintT l >> return x


labelOf :: Labeled l a -> l
labelOf (Lb l x) = l
labelOf (NTLb l x)=l
labelOf (RLb l x i)=l -- what about i???

relabel ::  Label l st => Labeled l a -> l -> SLIO l st f (Labeled l a)
relabel lblVal lbl = toLabeled lbl (unlabel lblVal)

newLIORef ::  Label l st => l -> a -> SLIO l st f (LIORef l a)
newLIORef l x = do guard l
                   ref <- io $ newIORef x
                   return (LIORef l ref)

readLIORef ::  Label l st => LIORef l a -> SLIO l st f a
readLIORef (LIORef l ref) = do taint l
                               io (readIORef ref)

writeLIORef ::  Label l st => LIORef l a -> a -> SLIO l st f ()
writeLIORef (LIORef l ref) v = do guard l
                                  io (writeIORef ref v)

labelOfRef :: LIORef l a -> l
labelOfRef (LIORef l ref) = l

toLabeled ::  Label l st => l -> SLIO l st f a -> SLIO l st f (Labeled l a)
toLabeled l m = SLIO (\s ->
                 let LIOState ll ss tt pp=  s in
                  traceShow ll $
                 do (x,LIOState lcurr scurr ntlab rlab) <- unSLIO m s
                    let checkPassed = traceShow ("lcurr:"++show lcurr) $ check scurr lcurr l
                    when (not checkPassed) (lioError "label check failed")
                    return (Lb l x, LIOState (nub ntlab++ll) ss (nub tt++ntlab) rlab))