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
-- module WLTrans (run, run1, whitelisting, wlrp) where
module Main
  ( main
  ) where

import Control.Monad.Trans.Maybe
import           Control.Monad.State.Strict
                                         hiding ( get
                                                , guard
                                                , put
                                                , modify
                                                )

--import Data.Biapplicative
import           Prelude                 hiding ( fail )

import qualified Data.HashMap.Strict           as HM
import           Data.HashSet            hiding ( map )
import           Data.Hashable
import           Data.List                      ( (\\)


                                                , union
                                                )
import           IFC
import           RP
import           SLIO
import NTTSLIO
import           SimpleStLIOUtil
import NWL
import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit
import Data.Monoid
import Control.Monad


newtype User = User String
  deriving (Eq, Show, Hashable)

newtype Rel l= Rel [(l, l)] deriving (Show)

instance Relation Rel User where
  lrt (Rel rel) l1 l2 = (l1, l2) `elem` rel
  getElements (Rel rel) = fromList $ concatMap (\(l1, l2) -> [l1, l2]) rel

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
  { SLIO.lset  = HM.empty
  , scurr = Rel [(User "Secret",User "Pub"), (User "Key", User "Pub")]
  , newid = 0
  }


initRPState :: RPState User
initRPState = RPState { r = (HM.empty, HM.empty) }

initNTTState :: NTTState User
initNTTState = NTTState {
                     ntlab = HM.empty
                     , assocnt = HM.empty
                     , NTTSLIO.lset = HM.empty
  }

initNWLState :: NWLState User
initNWLState = NWLState {
                     NWL.lset = HM.empty
                     , derivable = HM.empty
  }

-- allowNM :: (MonadIFC st (Rel User) Rel User m) => m ()
-- allowNM = do
--   Rel st <- getScurr <$> get
--   setUserState (Rel $ st ++ [(User "NSA", User "Military")])


disallowSP :: (MonadIFC st (Rel User) Rel User m) => m ()
disallowSP = do
  Rel st <- getScurr <$> get
  setUserState (Rel $ st \\ [(User "Secret"  , User "Pub" )])

wlrp :: (MonadIFC st (Rel User) Rel User m, MonadRP rp User Rel m, MonadNTT (nt User) User m, MonadNWL (NWLState User) User m) => m ()
wlrp = do
    secret <- label (User "Secret" ) "secret"
    k <- label (User "Key" ) "key"
    -- secret <- asRP unlabel [User "Pub"] secret
    
    pub <- toLabeled (User "Pub" ) (do 
      secret <- asRP unlabel [User "Pub"] secret
      k <- unlabel k
      asNWL $ label (User "Pub" ) (k ++ secret)
      return (k ++ secret)
      )
    -- pub <- label (User "Pub" ) (k ++ secret)
    disallowSP
    k <- unlabel k
    _ <- label (User "Pub" ) k
    return ()

whitelisting :: (MonadIFC st (Rel User) Rel User m, MonadRP rp User Rel m, MonadNTT (nt User) User m, MonadNWL (NWLState User) User m) => m ()
whitelisting = do
    secret <- label (User "Secret" ) "secret"
    k <- label (User "Key" ) "key"
    -- secret <- asRP unlabel [User "Pub"] secret
    
    pub <- toLabeled (User "Pub" ) (do 
      secret <- unlabel secret
      k <- unlabel k
      asNWL $ label (User "Pub" ) (k ++ secret)
      return (k ++ secret)
      )
    -- pub <- label (User "Pub" ) (k ++ secret)
    disallowSP
    k <- unlabel k
    _ <- label (User "Pub" ) k
    return ()

interact :: (MonadIFC st (Rel User) Rel User m, MonadRP rp User Rel m, MonadNTT (nt User) User m, MonadNWL (NWLState User) User m) => m ()
interact = do
    secret <- label (User "Secret" ) "secret"
    k <- label (User "Key" ) "key"
    -- secret <- asRP unlabel [User "Pub"] secret
    
    pub <- toLabeled (User "Pub" ) (do 
      -- s <- label (User "A1" ) "s"
      secret <- asNT unlabel secret
      k <- unlabel k
      asNWL $ label (User "Pub" ) (k ++ secret) 
      return (k ++ secret)
      )

    pub' <- toLabeled (User "Pub1" ) (do 
      secret <- unlabel pub
      k <- unlabel k
      asNWL $ label (User "Pub1" ) (k ++ secret)
      return (k ++ secret)
      )
    

    -- pub <- label (User "Pub" ) (k ++ secret)
    disallowSP
    k <- unlabel k
    _ <- label (User "Pub" ) k
    return ()

run act = do
    (r, s) <- runStateT (runStateT (runStateT (runStateT act initNWLState) initNTTState) initRPState) initState -- (runMaybeT rptt)
    print r
    print s
    return ()


run1 :: Show a => StateT (NTTState User) (StateT (RPState User) (StateT (NWLState User) (StateT (SLIOState (Rel User) User) IO))) a -> IO ()
run1 act = do
    (r, s) <- runStateT (runStateT (runStateT (runStateT act initNTTState) initRPState) initNWLState) initState -- (runMaybeT rptt)
    print r
    print s
    return ()

main :: IO ()
main = defaultMainWithOpts
       [testCase "whitelisting forbidden, stack: [wl (rp)]" $ run whitelisting
       , testCase "whitelisting forbidden, stack: [rp (wl)]" $ run1 whitelisting
       , testCase "wlrp allowed, stack: [wl (rp)]" $ run wlrp
       , testCase "wlrp allowed, stack: [rp (wl)]" $ run1 wlrp
       -- , testCase "ntrp forbidden" $ NTRPTrans.run ntrp
       ]
       mempty

-- instance MonadNTT (nt l) l m => MonadNTT (nt l) l (MaybeT m) where
--   asNT f ld= do
--     x <- f ld
--     _ <- lift (asNT (\_ -> return x) ld)
--     return x
--   getNTState    = lift getNTState
--   putNTState    = lift . putNTState
--   modifyNTState = lift . modifyNTState

-- instance MonadNWL (NWLState l) l m => MonadNWL (NWLState l) l (MaybeT m) where
--   asNWL f= do 
--     x <- f
--     _ <- lift (asNWL (do return x))
--     return x
--   getNWLState    = lift getNWLState
--   putNWLState    = lift . putNWLState

-- instance MonadRP rp l rel m => MonadRP rp l rel (MaybeT m) where
--   asRP f lst ld= do
--     x <- f ld
--     _ <- lift (asRP (\_ -> return x) lst ld)
--     return x
--   getRPState = lift getRPState
--   putRPState = lift . putRPState
--   modifyRPState = lift . modifyRPState
--   getRPRelation = lift getRPRelation

-- instance MonadIFC st scurr rel l m => MonadIFC st scurr rel l (MaybeT m) where
--   label l s = lift (label l s)
--   -- lebelInternal l s = lift (lebelInternal l s)
--   unlabel = lift . unlabel
--   guard b = lift (guard b)
--   setUserState = lift . setUserState
--   getRelation = lift getRelation
--   get = lift get
--   put = lift . put
--   modify = lift . modify
--   resetOP = do
--     rs <- lift resetOP
--     return
--       (do
--         lift rs)
--   toLabeled l m= do
--     rop <- resetOP
--     x <- m
--     lv <- label l x
--     rop
--     return lv
--   newIORefInternal l a= lift $ newIORefInternal l a
--   newIORef l a = lift $ newIORef l a
--   readIORef = lift . readIORef
--   writeIORefInternal lv b = lift (writeIORefInternal lv b)

--   writeIORef lv b = lift $ writeIORefInternal lv b
  -- writeIORefInternal = lift . writeIORefInternal
  

instance {-# OVERLAPS #-} (MonadRP rp l rel m, MonadNTT (nt l) l (StateT (nt l) m))
  => MonadRP rp l rel (StateT (nt l) m) where
  asRP f lst ld= do
    x <- f ld
    _ <- lift (asRP (\_ -> return x) lst ld)
    return x
  getRPState = lift getRPState
  putRPState = lift . putRPState
  modifyRPState = lift . modifyRPState
  getRPRelation lset= lift $ getRPRelation lset

instance  (MonadRP rp l rel m, MonadNWL (NWLState l)  l (StateT (NWLState l) m))
  => MonadRP rp l rel (StateT (NWLState l) m) where
  asRP f lst ld= do
    x <- f ld
    _ <- lift (asRP (\_ -> return x) lst ld)
    return x
  getRPState = lift getRPState
  putRPState = lift . putRPState
  modifyRPState = lift . modifyRPState
  getRPRelation lset= lift $ getRPRelation lset

instance  (MonadNTT (nt l) l m, MonadNWL (NWLState l) l (StateT (NWLState l) m))
  => MonadNTT (nt l) l (StateT (NWLState l) m) where
  asNT f ld= do
    x <- f ld
    _ <- lift (asNT (\_ -> return x) ld)
    return x
  getNTState    = lift getNTState
  putNTState    = lift . putNTState
  modifyNTState = lift . modifyNTState

-- instance  (MonadNTT (nt l) l m, MonadRP rp l rel (StateT rp m)) => MonadNTT (nt l) l (StateT rp m) where
--   asNT f ld= do
--     x <- f ld
--     _ <- lift (asNT (\_ -> return x) ld)
--     return x
--   getNTState    = lift getNTState
--   putNTState    = lift . putNTState
--   modifyNTState = lift . modifyNTState

instance (MonadNWL (nw l) l m, MonadNTT (NTTState l) l (StateT (NTTState l) m)) => MonadNWL (nw l) l (StateT (NTTState l) m) where
  asNWL f= do 
    x <- f
    _ <- lift (asNWL (do return x))
    return x
  getNWLState    = lift getNWLState
  putNWLState    = lift . putNWLState
  modifyNWLState = lift . modifyNWLState

instance (MonadNWL (nw l) l m, MonadRP (RPState l) l rel (StateT (RPState l) m)) => MonadNWL (nw l) l (StateT (RPState l) m) where
  asNWL f= do 
    x <- f
    _ <- lift (asNWL (do return x))
    return x
  getNWLState    = lift getNWLState
  putNWLState    = lift . putNWLState
  modifyNWLState = lift . modifyNWLState