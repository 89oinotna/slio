{-# LANGUAGE MultiParamTypeClasses, TupleSections #-}
{-# LANGUAGE FunctionalDependencies #-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
module SimpleStLIO
       (SLIO(..), Labeled,  LIORef, Label(..), LIOState(..), Replaying(..),
        label, unlabel, labelOf, relabel,
        getLabel, getState, setState,
        newLIORef, writeLIORef, readLIORef, labelOfRef,
        toLabeled, labelNT, unlabelReplaying, getReplaying)--, unlabelR)--, sfmap)
where



import Control.Applicative


import Prelude hiding (fail)
import Control.Monad.Fail (MonadFail (..))

import Control.Monad hiding (guard)
import Data.List
import Data.IORef
import Debug.Trace (traceShow)
import Data.Map (Map, lookup, insert, empty)
import Data.Maybe (Maybe)
import Data.Type.Equality
import Text.ParserCombinators.ReadPrec (reset)

-- the bool in rlab tracks the fact that a global unlabel has been done
-- the guard has to check that any info in the computation (unlabeled) can flow to the label 
-- we can replay information only if there wasnt any global unlabeling or if all of the replaying (all the ids from 0 to current) can flow to the label
data  (Label l st, Replaying r l st, Show (r l)) => LIOState l st r= LIOState { lcurr :: [l], scurr :: st, ntlab :: [l], rlab:: Map String (Int, [Int], [r l])}--, ids :: Map String Int }
  deriving (Show)



--data FlowTo l = FlowTo l l

class (Eq (r l), Show (r  l), Label l st) => Replaying r l st | r l -> st where
  -- TODO : use id info
  create :: l -> l -> Int -> [r l]
  checkR :: Map String (Int, [Int], [r l]) -> l -> l -> Bool
  -- inject :: (Label l st) => [r l] -> st -> st
  -- intersection :: [r l] -> [r l] -> [r l]

-- class (Eq (f l), Eq l) => FlowTo f l where
--   source :: f l -> l
--   target :: f l -> l

--instance FlowTo f a => Diff [] [] (f a) where
  --difference l1 l2= l1 \\ l2

newtype SLIO l st r a= SLIO { unSLIO :: LIOState l st r  -> IO (a, LIOState l st r ) }

instance Monad (SLIO l st r) where
  return x = SLIO (\s -> return (x, s))
  SLIO f >>= g = SLIO $ \s ->
    do (x,s') <- f s
       unSLIO (g x) s'

instance   MonadFail (SLIO l st r) where
  fail err = SLIO (\_ -> fail err)

instance Functor (SLIO l st r) where
  fmap = liftM

instance Applicative (SLIO l st r) where
  pure = return
  (<*>) = ap

class (Eq l, Show l) => Label l st where
  -- check to ensure that l1 lis less restricrtive than l2 in s
  lrt :: Replaying r l st => st -> [l] -> Map String (Int, [Int], [r l]) -> l -> l -> Bool

  -- TODO: what about incupperset and replaying?
  -- to avoid to conditional allow a flow
  incUpperSet :: Replaying r l st => st -> st -> [l] -> Map String (Int, [Int], [r l]) -> l -> Bool

data Labeled l a  = Lb l a Int| NTLb l a Int
             deriving (Eq, Show)


data LIORef l a = LIORef l (IORef a)

lioError s = fail s

-- internal primitives

getLabel :: (Replaying r l st,Label l st) => SLIO l st r [l]
getLabel = SLIO (\s -> return (lcurr s, s))

getState ::  (Replaying r  l st,Label l st)=> SLIO l st r st
getState = SLIO (\s -> return (scurr s, s))

getReplaying :: (Label l st, Replaying r  l st) => SLIO l st r (Map String (Int, [Int], [r l]))
getReplaying = SLIO (\s -> return (rlab s, s))

-- getReplaying ::  Label l st => SLIO l st r (Map String (Int, [(,) Int l]))
-- getReplaying = SLIO (\s -> return (rlab ids s, s))

setState ::  (Replaying r  l st,Label l st) => st -> SLIO l st r ()
setState st = SLIO (\(LIOState lcurr scurr ntlab rlab ) ->
                      do when (any (incUpperSet scurr st lcurr rlab ) lcurr) (lioError "incUpperClosure check failed")
                         return ((), LIOState lcurr st ntlab rlab ))


check :: (Replaying r l st)  => st -> [l] -> Map String (Int, [Int], [r l]) -> l -> Bool
check scurr lcurr rlab l = and [ lrt scurr lcurr rlab x l | x <- lcurr ]

guard ::  (Replaying r  l st,Label l st) => l -> SLIO l st r ()
guard l = do lcurr <- getLabel
             scurr <- getState
             rlab <- getReplaying
             let checkPassed = check scurr lcurr rlab l
             unless checkPassed (lioError "label check failed")

io ::  Label l st => IO a -> SLIO l st r a
io m = SLIO (\s -> fmap (,s) m)

-- exported functions

label ::  (Replaying r  l st,Label l st)=> l -> a -> SLIO l st r (Labeled l a)
label l x = do
  guard l
  i <- getNewId l
  return (Lb l x i)

-- NOTE: non transitive values are managed by adding their label to lcurr (coming from toLabeled)
labelNT ::  (Replaying r  l st,Label l st) => l -> a -> SLIO l st r (Labeled l a)
labelNT l x = do
  guard l
  i <- getNewId l
  return (NTLb l x i)

getNewId :: (Replaying r  l st,Label l st) => l -> SLIO l st r Int
getNewId l= SLIO (\(LIOState lcurr scurr ntlab rlab) ->
  let k = show l in
    case Data.Map.lookup (show l) rlab of
        Nothing -> return (0, LIOState lcurr scurr ntlab $ Data.Map.insert k (1, [], []) rlab)
        Just (n, b, l) -> return (n, LIOState lcurr scurr ntlab $ Data.Map.insert k (n+1, b, l) rlab)
  )

-- labelR :: (Label l st) => l -> a -> SLIO l st (Labeled l a)
-- labelR l x= do
--               guard l
--               i <- createLabel l
--               return (RLb l x i)

-- createLabel :: (Label l st) => l -> SLIO l st r Int
-- createLabel l= SLIO (\(LIOState lcurr scurr ntlab rlab ids) ->
--   let insert n lst=Data.Map.insert (show l) (n,lst) rlab ids
--     in
--   case Data.Map.lookup (show l) (rlab ids) of
--     Just (n, lst) -> let nrlab ids = insert (n+1) lst in return (n + 1 , LIOState lcurr scurr ntlab nrlab)
--     Nothing -> let nrlab ids = insert 1 [] in return (1 , LIOState lcurr scurr ntlab  nrlab)
--   )
    --createFlows l lcurr = [ (l, ll) | ll <- lcurr]
    --insert n [] lcurr=Data.Map.insert (show l) (n,createFlows (n) lcurr) 
    --insert n lst lcurr=Data.Map.insert (show l) (n, lst ++ createFlows (n) lcurr)

-- resetReplaying :: (Label l st, Replaying r Int l st) => l -> SLIO l st r ()
-- resetReplaying l = SLIO (\(LIOState lcurr scurr ntlab rlab ids ) ->
--             let toReset (x:xs) = create l x ++ toReset xs
--                 toReset [] = []  in
--             return ((), LIOState lcurr scurr ntlab (rlab  \\ traceShow ("reset" ++ show (toReset lcurr)) toReset lcurr) ids))


nonReplaying :: (Replaying r l st, Show a) => a -> Int -> SLIO l st r ()
nonReplaying l id= --TODO: use id??
  let k= show l in
  SLIO (\(LIOState lcurr scurr ntlab rlab) ->
    let nrlab = case Data.Map.lookup k rlab of
                Just (i, ids, l) -> Data.Map.insert k (i, nub $ id:ids, l) rlab
    in
    return ((), LIOState lcurr scurr ntlab nrlab)
    )

-- TODO: set true in rlab
unlabel ::  (Replaying r  l st,Label l st) => Labeled l a -> SLIO l st r a
unlabel (Lb l x i) = nonReplaying l i >> unlabelInternal l x --resetReplaying l >> return x
unlabel (NTLb l x i)= taintNT l >> nonReplaying l i>> unlabelInternal l x--resetReplaying l >> return x

unlabelInternal l x= taint l >>  return x

valueOf :: Labeled l a -> a
valueOf(Lb l x i) = x
valueOf(NTLb l x i) = x


unlabelReplaying :: (Replaying r  l st,Label l st) => Labeled l a -> [l] -> SLIO l st r a
unlabelReplaying ld ls =
  let
    l = labelOf ld
    i = idOf ld
    x = valueOf ld
    rls (x:xs)= create l x i ++ rls xs
    rls []=[] in
    checkFlow l ls >> taintR l (rls ls) >> unlabel ld
-- taintAll :: Label l st => [l] -> SLIO l st r ()
-- taintAll = foldr ((>>) . taint) (return ())

-- to check that when replaying the flow is allowed (replaying flow) 
-- NOTE: you cannot say to replay a not existing flow
checkFlow :: (Replaying r  l st,Label l st) => l -> [l] -> SLIO l st r ()
checkFlow l ls=do
  scurr <- getState
  rlab <- getReplaying
  let checkPassed = all (check scurr [l] rlab) ls
  unless checkPassed (lioError "check flow while replaying failed")

-- unlabelAsReplaying :: Label l st => Labeled l b -> [l] -> SLIO l st r b
-- unlabelAsReplaying ldata lst@(x:xs)=do
--   taintAll xs
--   d <- relabel ldata x
--   unlabel d

taintR :: (Replaying r  l st, Label l st) => l -> [r  l] -> SLIO l st r ()
taintR l ls = SLIO (\(LIOState lcurr scurr ntlab rlab) ->
  let k = show l in
  case Data.Map.lookup k rlab of
    Nothing -> lioError "It is impossible to have a labeled data without knowing that you have it"
    Just (id, b, l) -> return ((), LIOState lcurr scurr ntlab $ Data.Map.insert k (id, b, nub ls++l) rlab))




-- unlabelR :: (Eq l,Show l) => Labeled l b -> [l] -> SLIO l st r b
-- --unlabelR (Lb l x) rsinks= taintR l rsinks >> return x -- not tainting lcurr (but in the guard for label then one needs to check also in rlab ids)
-- unlabelR (NTLb l x) rsinks= taintR l rsinks >> return x -- not tainting lcurr (but in the guard for label then one needs to check also in rlab ids)
-- unlabelR (Lb l x) rsinks= taintR l rsinks >> return x -- not tainting lcurr (but in the guard for label then one needs to check also in rlab ids)

taint ::  (Replaying r  l st,Label l st) => l -> SLIO l st r ()
taint l = SLIO (\(LIOState lcurr scurr ntlab rlab) -> return ((), LIOState (nub (l : lcurr)) scurr ntlab rlab))

taintNT ::  (Replaying r  l st,Label l st)=> l -> SLIO l st r ()
taintNT l = SLIO (\(LIOState lcurr scurr ntlab rlab) -> return ((), LIOState lcurr scurr (nub (l : ntlab)) rlab))

-- taintR :: (Eq l, Show l) => l -> [l] -> SLIO l st r (Map String (Int, [(Int, l)]))
-- taintR l rsinks= SLIO (\(LIOState lcurr scurr ntlab rlab ids) ->
--   let insert n lst=Data.Map.insert (show l) (n,lst) rlab ids
--       createFlows l = [ (l, ll) | ll <- rsinks]
--     in
--        case Data.Map.lookup (show l) (rlab ids) of
--         Just (n, lst) -> let nrlab ids = (insert n $ nub lst++createFlows n) in return (nrlab , LIOState lcurr scurr ntlab nrlab)
--       --Nothing -> let nrlab ids = (insert 1 $ createFlows 1) in return (1 , LIOState lcurr scurr ntlab  nrlab)
--   )

-- unlabelT :: Label l st => TransientLabeled l a -> SLIO l st a
-- unlabelT (TLb l x) = taint l >> taintT l >> return x


labelOf :: Labeled l a -> l
labelOf (Lb l x _) = l
labelOf (NTLb l x _)=l

idOf :: Labeled l a -> Int
idOf (Lb l x i) = i
idOf (NTLb l x i)=i

relabel ::  (Replaying r  l st,Label l st) => Labeled l a -> l -> SLIO l st r (Labeled l a)
relabel lblVal lbl = toLabeled lbl (unlabel lblVal)

newLIORef ::  (Replaying r  l st,Label l st) => l -> a -> SLIO l st r (LIORef l a)
newLIORef l x = do guard l
                   ref <- io $ newIORef x
                   return (LIORef l ref)

readLIORef ::  (Replaying r  l st,Label l st) => LIORef l a -> SLIO l st r a
readLIORef (LIORef l ref) = do taint l
                               io (readIORef ref)

writeLIORef ::  (Replaying r  l st,Label l st) => LIORef l a -> a -> SLIO l st r ()
writeLIORef (LIORef l ref) v = do guard l
                                  io (writeIORef ref v)

labelOfRef :: LIORef l a -> l
labelOfRef (LIORef l ref) = l

-- what about replaying in a toLabekled???
toLabeled ::  (Replaying r  l st,Label l st) => l -> SLIO l st r a -> SLIO l st r (Labeled l a)
toLabeled l m = SLIO (\s ->
                 let LIOState ll ss tt rr=  s in
                  traceShow ll $
                 do (x,LIOState lcurr scurr ntlab rlab) <- unSLIO m s
                    let checkPassed = traceShow ("lcurr:"++show lcurr) $ check scurr lcurr rr l
                    unless checkPassed (lioError "label check failed")
                    return (x, LIOState (nub ntlab++ll) ss (nub tt++ntlab) rlab)) >>=
                  (\x -> do
                    i <- getNewId l
                    return (Lb l x i))