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
module Main
  ( main
  ) where



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
  , scurr = Rel [(User "NSA", User "Military")]
  , newid = 0
  }

initRPState :: RPState User
initRPState = RPState { r = (HM.empty, HM.empty) }


disallowNM :: (MonadIFC st (Rel User) Rel User m) => m ()
disallowNM = do
  Rel st <- getScurr <$> get
  setUserState (Rel $ st \\ [(User "NSA", User "Military")])



replaying
  :: StateT (RPState User) (StateT (SLIOState (Rel User) User) IO) String -- SLIO User Rel (Rep) String
replaying = do
  file1 <- label (User "NSA") "secret"
  -- file2 <- label (User "NSA") "secret"
  file  <- asRP (unlabel) [User "Military"] file1
  -- file  <- unlabel  file2
  mil   <- label (User "Military") file

  disallowNM

  label (User "Military") file
  --mil   <- newLIORef (User "Military") file
  -- mil   <- newLIORef (User "Another") $ file++"A"
  --writeLIORef mil file
  unlabel mil


main :: IO ()
main = do
  (r, s) <- runStateT (runStateT replaying initRPState) initState
  print r
  print s

