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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module IFC
  ( MonadIFC(..)
  , HasLSet(..)
  , HasLVIds(..)
--   , HasRelation(..)
  ,HasScurr(..)
  , ToRelation(..)
  , Relation(..)
  , MutableRelation(..)
  , Labeled(..)
  , LIORef(..)
  , LV(..)
  ) where



-- import Control.Monad.Trans.State.Strict
import           Control.Monad.State.Strict hiding (guard, get, put)

--import Data.Biapplicative

import           Prelude                 hiding ( fail )

-- import           Debug.Trace                    ( traceShow )
import qualified Data.HashMap.Strict           as HM
import           Data.Hashable
import           Data.IORef                     ( IORef
                                                
                                                
                                                
                                                )
import Data.HashSet


class HasLSet st l | st -> l where
  getLSet :: st -> HM.HashMap l [Int]
  setLSet :: HM.HashMap l [Int] -> st -> st
  modifyLSet :: (HM.HashMap l [Int] -> HM.HashMap l [Int]) -> st -> st
  modifyLSet m st = setLSet (m (getLSet st)) st

class HasLVIds st where
  getId :: st -> Int
  setId :: Int -> st -> st
  incId :: st -> st

-- class Relation rel l => HasRelation st rel l | st l -> rel  where
--   getRel :: st l -> rel l
--   setRel :: rel l -> st rel l -> st rel l

class HasScurr st scurr | st -> scurr where
  getScurr :: st -> scurr
  setScurr :: scurr -> st -> st

class (Eq l, Show l, Hashable l) => Relation rel l where
  lrt :: rel l -> l -> l -> Bool-- rel -> l -> l -> Bool --
  getElements :: rel l -> HashSet l

class Relation rel l => MutableRelation rel l where
  incUpperSet :: rel l -> rel l -> l -> Bool
  incUpperSet oldRel newRel l=any (\el -> not (lrt oldRel l el) &&  lrt newRel l el) (getElements newRel)

class Relation rel l => ToRelation scurr rel l | scurr -> rel l where
    toRelation :: scurr -> rel l

class -- (MonadState (st rel l) m, 
    -- (HasRelation st rel l, 
    (HasScurr (st scurr l) scurr,
    MutableRelation rel l, HasLSet (st scurr l) l, 
    HasLVIds (st scurr l), MonadFail m, MonadIO m,
    ToRelation scurr rel l
    ) 
    => MonadIFC st scurr rel l m | m -> st scurr l where
  
  label ::  l -> a -> m (Labeled l a)

  unlabel ::  Labeled l a -> m a

  guard ::  l -> m ()

  setUserState ::  scurr -> m ()

  getRelation ::  m (rel l)
  
  toLabeled ::  l -> m a -> m (Labeled l a)
  resetOP :: m (m ())
  
  -- User must not use those functions
  get :: m (st scurr l)
  put :: (st scurr l) -> m ()
  modify :: (st scurr l -> st scurr l) -> m ()


data Labeled l a = Lb
  { labelOf :: l
  , valueOf :: a
  , idOf    :: Int
  }
  deriving (Eq, Show)

data LIORef l a = LIORef
  { labelOfRef :: l
  , _lioRefVal :: IORef a
  , lioRefInt  :: Int
  }


class LV t l where
  getLabel' :: t l a -> l
  getId'    :: t l a -> Int

instance LV LIORef l  where
  getLabel' = labelOfRef
  getId'    = lioRefInt

instance LV Labeled l  where
  getLabel' = labelOf
  getId'    = idOf





