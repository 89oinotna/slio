{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FunctionalDependencies #-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DatatypeContexts #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
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
  -- , labelNT
  , unlabelReplaying
  , getReplaying
  , asNT
  , asRP
  )--, unlabelR)--, sfmap)
    where



import           Control.Applicative


import           Control.Monad.Fail             ( MonadFail(..) )
import           Prelude                 hiding ( fail )

import Control.Monad ( MonadFail(fail), ap, liftM, unless, when )
import Data.IORef ( newIORef, readIORef, writeIORef, IORef )
import Data.List ( nub )
import  qualified         Data.Map                     ( Map
                                                , empty
                                                , insert
                                                , lookup, keys, unionWith
                                                )
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
  , rlab  :: r l
  , newid :: Int
  }--, ids :: Map String Int }
  deriving Show



--data FlowTo l = FlowTo l l
data R l l1 = Rep Int l l1
  deriving (Eq, Show)

class (Show (r  l), Label l st r) => Replaying r l st | r l -> st where
  -- TODO : use id info
  -- getNewId ::  l -> SLIO l st r Int

  -- trackUnlabel :: l -> Int -> SLIO l st r ()

  addPromises :: l -> Int -> [l] -> SLIO l st r ()

  replayTo :: l -> SLIO l st r ()


  --create :: l -> l -> Int -> [r l]
  --checkR :: r l -> l -> l -> Bool
  -- inject :: (Label l st r) => [(r l, Bool)] -> st -> st
  -- intersection :: [(r l, Bool)] -> [r l] -> [r l]

-- class (Eq (f l), Eq l) => FlowTo f l where
--   source :: f l -> l
--   target :: f l -> l

--instance FlowTo f a => Diff [] [] (f a) where
  --difference l1 l2= l1 \\ l2

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
  lrt :: st -> HM.HashMap l [Int] -> r l -> l -> l -> Bool

  -- to avoid to conditional allow a flow
  incUpperSet :: st -> st -> HM.HashMap l [Int] -> r l -> r l -> l -> Bool

data Labeled l a  = Lb l a Int
             deriving (Eq, Show)

data LIORef l a = LIORef l (IORef a) Int


-- class LV a where

lioError s = fail s

-- internal primitives

getLabel :: (Replaying r l st, Label l st r) => SLIO l st r (HM.HashMap l [Int])
getLabel = SLIO (\s -> return (lcurr s, s))

getState :: (Replaying r l st, Label l st r) => SLIO l st r st
getState = SLIO (\s -> return (scurr s, s))

getReplaying
  :: (Label l st r, Replaying r l st)
  => SLIO l st r (r l)
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


check
  :: (Label l st r)
  => st
  -> HM.HashMap l [Int]
  -> r l
  -> l
  -> Bool
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

-- exported functions

-- Used to check if allowing the replay is causing an increaseUpperSet
checkAndRep ::(Replaying r l st, Label l st r) => l -> SLIO l st r ()
checkAndRep l=  SLIO (\s@(LIOState lcurr scurr ntlab rlab newid) -> do
    (_, LIOState _ _ _ rlab' _) <- unSLIO (replayTo l) s
    when (any (incUpperSet scurr scurr lcurr rlab rlab') $ HM.keys lcurr)
         (lioError "incUpperClosure check failed")
    return ((), LIOState lcurr scurr ntlab rlab' newid)
  )

label
  :: (Replaying r l st, Label l st r) => l -> a -> SLIO l st r (Labeled l a)
label l x = do
  guard l
  checkAndRep l
  --replayTo l
  Lb l x <$> getNewId


-- labelNT
--   :: (Replaying r l st, Label l st r) => l -> a -> SLIO l st r (Labeled l a)
-- labelNT l x = do
--   guard l
--   activateRepRel l
--   i <- getNewId l
--   return (NTLb l x i)

getNewId :: (Replaying r l st, Label l st r) => SLIO l st r Int
getNewId = SLIO
  (\(LIOState lcurr scurr ntlab rlab newid) ->
    -- let k = show l
    -- in
    --   case HM.lookup (show l) rlab of
    --     Nothing -> return
    --       (0, LIOState lcurr scurr ntlab $ HM.insert k (1, [], []) rlab)
    --     Just (n, b, l) ->
          return
            ( newid
            --, LIOState lcurr scurr ntlab $ HM.insert k (n + 1, b, l) rlab
            , LIOState lcurr scurr ntlab rlab $ newid + 1
            )
  )

-- labelR :: (Label l st r) => l -> a -> SLIO l st (Labeled l a)
-- labelR l x= do
--               guard l
--               i <- createLabel l
--               return (RLb l x i)

-- createLabel :: (Label l st r) => l -> SLIO l st r Int
-- createLabel l= SLIO (\(LIOState lcurr scurr ntlab rlab newid ids) ->
--   let insert n lst=HM.insert (show l) (n,lst) rlab ids
--     in
--   case HM.lookup (show l) (rlab ids) of
--     Just (n, lst) -> let nrlab ids = insert (n+1) lst in return (n + 1 , LIOState lcurr scurr ntlab nrlab)
--     Nothing -> let nrlab ids = insert 1 [] in return (1 , LIOState lcurr scurr ntlab  nrlab)
--   )
    --createFlows l lcurr = [ (l, ll) | ll <- lcurr]
    --insert n [] lcurr=HM.insert (show l) (n,createFlows (n) lcurr) 
    --insert n lst lcurr=HM.insert (show l) (n, lst ++ createFlows (n) lcurr)

-- resetReplaying :: (Label l st r, Replaying r Int l st) => l -> SLIO l st r ()
-- resetReplaying l = SLIO (\(LIOState lcurr scurr ntlab rlab newid ids ) ->
--             let toReset (x:xs) = create l x ++ toReset xs
--                 toReset [] = []  in
--             return ((), LIOState lcurr scurr ntlab (rlab  \\ traceShow ("reset" ++ show (toReset lcurr)) toReset lcurr) ids))


-- trackUnlabel :: (Label l st r, Show a) => a -> Int -> SLIO l st r ()
-- trackUnlabel l id = --TODO: use id??
--   let k = show l
--   in  SLIO
--         (\(LIOState lcurr scurr ntlab rlab newid) ->
--           let nrlab = case HM.lookup k rlab of
--                 Just (i, ids, l) ->
--                   HM.insert k (i, nub $ id : ids, l) rlab
--           in  return ((), LIOState lcurr scurr ntlab nrlab)
--         )

-- TODO: set true in rlab
unlabel :: (Replaying r l st, Label l st r) => Labeled l a -> SLIO l st r a
unlabel (Lb   l x i) = {-trackUnlabel l i >>-} unlabelInternal l i x --resetReplaying l >> return x

-- NOTE: non transitive values are managed by adding their label to lcurr (coming from toLabeled)
unlabelNT :: (Replaying r l st, Label l st r) => Labeled l a -> SLIO l st r a
unlabelNT (Lb l x i) = taintNT l i {-}>> trackUnlabel l i -}>> unlabelInternal l i x--resetReplaying l >> return x

unlabelInternal l i x = taint l i>> return x

valueOf :: Labeled l a -> a
valueOf (Lb   l x i) = x
-- valueOf (NTLb l x i) = x

asNT :: (Replaying r l st, Label l st r) => (Labeled l a -> SLIO l st r a)-> Labeled l a -> SLIO l st r a
asNT f ld@(Lb l a i) = do
  taintNT l i
  f ld

asRP :: (Replaying r l st, Label l st r) => (Labeled l a -> SLIO l st r a)->[l] -> Labeled l a -> SLIO l st r a
asRP f lst ld@(Lb l a i)= do
  addPromises l i lst
  f ld

-- asNT (asReplaying [] unlabel) (Lb l a i)

--asNT (\x -> asReplaying [] (ulabel) x) lv

--asReplaying :: [l] -> (f -> Labeled l a -> SLIO) -> f -> Labeled l a -> SLIO

unlabelReplaying
  :: (Replaying r l st, Label l st r) => Labeled l a -> [l] -> SLIO l st r a
unlabelReplaying ld ls =
  let l = labelOf ld
      i = idOf ld
      --rls (x : xs) = create l x i ++ rls xs
      --rls []       = []
  in  {-checkFlow l ls >>-} addPromises l i ls >> unlabel ld


-- to check that when replaying the flow is allowed (replaying flow) 
-- NOTE: you cannot say to replay a not existing flow
-- checkFlow :: (Replaying r l st, Label l st r) => l -> [l] -> SLIO l st r ()
-- checkFlow l ls = do
--   scurr <- getState
--   rlab  <- getReplaying
--   let checkPassed = all (check scurr [l] rlab) ls
--   unless checkPassed (lioError "check flow while replaying failed")



-- promiseRepRel
--   :: (Replaying r l st, Label l st r) => l -> [r l] -> SLIO l st r ()
-- promiseRepRel l ls = SLIO
--   (\(LIOState lcurr scurr ntlab rlab newid) ->
--     let k = show l
--     in
--       let newrls oldrls = map (, False) $ filter (`notElem` oldrls) ls
--       in
--         case HM.lookup k rlab of
--           Nothing ->
--             lioError
--               "It is impossible to have a labeled data without knowing that you have it"
--           Just (id, b, l) -> return
--             ( ()
--             , LIOState lcurr scurr ntlab
--               $ HM.insert k (id, b, l ++ newrls (map fst l)) rlab
--             )
--   )


-- taintRepRel :: (Replaying r l st, Label l st r) => l -> SLIO l st r ()
-- taintRepRel lab= SLIO
--   (\(LIOState lcurr scurr ntlab rlab newid) ->
--     let nrlab = foldr
--           (\l acc -> case HM.lookup (show l) acc of
--             Nothing            -> acc
--             Just (id, lids, l) -> HM.insert (show l)
--               ( id , lids
--               , map
--                 (\c@(rl, _) -> if rid rl `elem` lids && trg rl == lab then (rl, True) else c)
--                 l
--               )
--               acc
--           )
--           rlab
--           lcurr
--     in  return ((), LIOState lcurr scurr ntlab nrlab)
--   )


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

-- promiseRepRel :: (Eq l, Show l) => l -> [l] -> SLIO l st r (Map String (Int, [(Int, l)]))
-- promiseRepRel l rsinks= SLIO (\(LIOState lcurr scurr ntlab rlab newid ids) ->
--   let insert n lst=HM.insert (show l) (n,lst) rlab ids
--       createFlows l = [ (l, ll) | ll <- rsinks]
--     in
--        case HM.lookup (show l) (rlab ids) of
--         Just (n, lst) -> let nrlab ids = (insert n $ nub lst++createFlows n) in return (nrlab , LIOState lcurr scurr ntlab nrlab)
--       --Nothing -> let nrlab ids = (insert 1 $ createFlows 1) in return (1 , LIOState lcurr scurr ntlab  nrlab)
--   )

-- unlabelT :: Label l st r => TransientLabeled l a -> SLIO l st a
-- unlabelT (TLb l x) = taint l >> taintT l >> return x


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
  --replayTo l
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
  --replayTo l
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
      (\s@(LIOState ll ss tt rr nid) ->
        traceShow ll $ do
              (x, LIOState lcurr scurr ntlab rlab newid) <- unSLIO m s
              let checkPassed = traceShow ("lcurr:" ++ show lcurr)
                    $ check scurr lcurr rr l
              unless checkPassed (lioError "label check failed")
              return (x, LIOState (HM.unionWith List.union ntlab ll) ss (HM.unionWith List.union tt ntlab) rlab nid)
      )
    >>= (\x -> do
          Lb l x <$> getNewId
        )
