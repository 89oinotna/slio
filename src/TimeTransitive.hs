{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE InstanceSigs           #-}
module TimeTransitive where

import DypIFC
import Data.HashSet
import qualified Control.Monad.State.Class     as State
import           Control.Monad.State.Strict
                                         hiding ( get
                                                , guard
                                                , modify
                                                , put
                                                )
import Control.Monad.RWS (MonadState(get))

-- TODO: policy transitivity

data IFCState ps l = IFCState
  { lset  :: Lset l
  , ps :: ps
  , newid :: Id
  }
  deriving Show

instance HasLSet (IFCState ps l) l where
    getLSet' = lset
    setLSet' ls st = st { lset = ls}

instance HasId (IFCState ps l) where
    getId = newid
    setId i st = st { newid = i }
    incId st = st { newid = 1 + newid st}

instance HasPolicy (IFCState ps l) ps where
    getPolicy' = ps
    setPolicy' p st = st { ps = p}

type User = String

newtype Relation = Relation (HashSet (User, User))

instance Rel Relation User where
    lrt l1 l2 (Relation rel) = member (l1,l2) rel

type PolicyState = Relation

instance Policy PolicyState User where
    canflow l1 _ l2 ps = lrt l1 l2 ps

instance IFCInternal User (IFCState PolicyState User) PolicyState where
    opLabel _ _ = id
    opUnlabel _ _ = id
    opToLabeledRet st l i st0 = setLSet' (lset st) st0
    guard l st = all (\(l', i') -> canflow l' i' l (ps st)) (lset st)
    opState st p = st { ps = p}
    stateGuard st _ st' = any (incUpperSet (ps st) (ps st')) (toList $ getLSet' st)

incUpperSet :: PolicyState -> PolicyState -> (User, i) -> Bool
incUpperSet o n (l, i)=any (\el -> not (canflow l i el o) && canflow l i el n) (getElements n)

getElements :: PolicyState -> [User]
getElements (Relation s)= Data.HashSet.foldr (\(l1, l2) acc -> l1:l2:acc) [] s

instance IFC User (IFCState PolicyState User) PolicyState (StateT (IFCState PolicyState User) IO ) where