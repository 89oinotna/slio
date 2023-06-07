{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module NTRPTrans 
(run, ntrp) where
-- module Main
--   ( main
--   ) where


import           Control.Monad.State.Strict
                                         hiding ( get
                                                , guard
                                                , put
                                                )

--import Data.Biapplicative
import           Prelude                 hiding ( fail )

import qualified Data.HashMap.Strict           as HM
import           Data.HashSet            hiding ( map )
import           Data.Hashable
import           Data.List                      ( (\\)
                                                , groupBy
                                                , nub
                                                , union
                                                )
import           IFC
import           RP
import           SLIO
import NTTSLIO
import           SimpleStLIOUtil


newtype User = User String
  deriving (Eq, Show, Hashable)

newtype Rel l= Rel [(l, l)] deriving (Show )

instance Relation Rel User where
  lrt (Rel rel) l1 l2 = (l1, l2) `elem` rel
  getElements (Rel rel) = fromList $ concat $ map (\(l1, l2) -> [l1, l2]) rel

instance Relation Rel User => MutableRelation Rel User where
  union (Rel r1) (Rel r2) = Rel $ reflTransClosure $ Data.List.union r1 r2
-- instance HasScurr (SLIOState (Rel l) l) (Rel l) where
--     getScurr = scurr

instance Relation Rel l => ToRelation (Rel l) Rel l where
  toRelation = id

instance Relation Rel l => ToRelation (RPState l) Rel l where
  toRelation (RPState (rplset, rp)) = Rel $ reflTransClosure rel   where
    labels = Data.List.union
      (HM.keys rplset)
      (concatMap (\(l1, _, l2, _) -> [l1, l2]) (concat $ HM.elems rp))
    rel =
      [ (l1, l2)
      | l1 <- HM.keys rplset
      , l2 <- labels
      , all (all (\i -> elem (l1, i, l2, True) (HM.lookupDefault [] l1 rp)))
        $ HM.lookup l1 rplset
      ]
      -- elems = 
      -- rel = [(l1, l2) | ]
      -- checkRep = case HM.lookup lbl1 nrlab of
      -- Nothing    -> False
      -- Just rplTo -> case HM.lookup lbl1 lset of
      --   Nothing  -> False
      --   Just lst -> all (\i -> (lbl1, i, lbl2, True) `elem` rplTo) lst --for all the ids there is the flow



initState :: SLIOState (Rel User) User
initState = SLIOState
  { lset  = HM.empty
  , scurr = Rel
              [(User "NSA", User "Military"), (User "Military", User "Another")]
  , newid = 0
  }


initRPState :: RPState User
initRPState = RPState { r = (HM.empty, HM.empty) }

initNTTState :: NTTState User 
initNTTState = NTTState {
                     ntlab = HM.empty
                     , assocnt = HM.empty
  }

disallowNM :: (MonadIFC st (Rel User) Rel User m) => m ()
disallowNM = do
  Rel st <- getScurr <$> get
  setUserState (Rel $ st \\ [(User "NSA", User "Military")])

disallowMB :: (MonadIFC st (Rel User) Rel User m) => m ()
disallowMB = do
  Rel st <- getScurr <$> get
  setUserState (Rel $ st \\ [(User "Military", User "Bob")])

allowMB :: (MonadIFC st (Rel User) Rel User m) => m ()
allowMB = do
  Rel st <- getScurr <$> get
  setUserState (Rel $ st ++ [(User "Military", User "Bob")])

allowNM :: (MonadIFC st (Rel User) Rel User m) => m ()
allowNM = do
  Rel st <- getScurr <$> get
  setUserState (Rel $ st ++ [(User "NSA", User "Military")])



ntrp :: (MonadIFC st (Rel User) Rel User m, MonadRP rp User Rel m, MonadNTT (nt User) User m) => m Integer
ntrp = do
  file <- label (User "NSA") 0
  x <- toLabeled (User "Military") $ do
                --   asRP unlabel [User "Military"] file
                  asRP (asNT unlabel) [User "Military"] file
                  -- asNT unlabel file
  disallowNM
  allowMB
  unlabel x
  b <- toLabeled (User "Bob") (unlabel file)
  unlabel b

run act =do
  (r, s) <-  runStateT (runStateT (runStateT act initNTTState) initRPState) initState -- (runMaybeT rptt)
  print r
  print s 

-- main :: IO ()
-- main = do
--   (r, s) <-  runStateT (runStateT (runStateT rptt initNTTState) initRPState) initState -- (runMaybeT rptt)
--   print r
--   print s

instance  (MonadRP rp l rel m, MonadNTT (NTTState l)  l (StateT (NTTState l) m))
  => MonadRP rp l rel (StateT (NTTState l) m) where
  asRP f lst ld= do
    x <- f ld
    _ <- lift (asRP (\_ -> return x) lst ld)
    return x
  getRPState = lift getRPState
  putRPState = lift . putRPState
  modifyRPState = lift . modifyRPState
  getRPRelation = lift getRPRelation

-- instance MonadIFC st scurr rel l m => MonadIFC st scurr rel l (MaybeT m) where







   
-- secure :: SLIO User Rel Rep Integer
-- secure = do
--   n <- label (User "NSA") 0
--   m <- toLabeled (User "Military") $ do
--         asRP (unlabel) [User "Military"] n
--   disallowNM
--   allowMB
--   relabel n (User "Bob") 
--   return 0
  --unlabel b



