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
module Main (main)
    where



import Control.Monad.State.Strict hiding (guard, get, put)

--import Data.Biapplicative
import           Prelude                 hiding ( fail )

import qualified Data.HashMap.Strict as HM
import Data.Hashable
import IFC
import           SimpleStLIOUtil
import NTTSLIO
import SLIO
import Data.HashSet hiding (map)

newtype User = User String
  deriving (Eq, Show, Hashable)

newtype Rel l= Rel [(l, l)] deriving (Show )

instance Relation Rel User where
    lrt (Rel rel) l1 l2 = (l1, l2) `elem` s
        where
            s = reflTransClosure rel
    getElements (Rel rel)= fromList $ concat $ map (\(l1, l2) -> [l1,l2]) rel

instance Relation Rel User => MutableRelation Rel User where

-- instance HasScurr (SLIOState (Rel l) l) (Rel l) where
--     getScurr = scurr

instance Relation Rel l => ToRelation (Rel l) Rel l where
    toRelation = id

initState :: SLIOState (Rel User) User
initState = SLIOState { lset = HM.empty
                     , scurr = Rel [(User "Input", User "Sanitizer")]
                     , newid = 0 }

initNTTState :: NTTState User 
initNTTState = NTTState {
                     ntlab = HM.empty
                     , assocnt = HM.empty
  }



disallowIS :: (MonadIFC st (Rel User) Rel User m) => m ()  --SLIO User Rel Rep ()
disallowIS = do
    setUserState (Rel [])

allowSD :: (MonadIFC st (Rel User) Rel User m) => m ()
allowSD = do
    rel <- getRelation
    let (Rel st) = rel
    setUserState (Rel $ st ++ [(User "Sanitizer", User "DB")])

escape :: (MonadIFC st (Rel User) Rel User m, MonadNTT (NTTState User) User m) => Labeled User String -> m (Labeled User String)
escape input= toLabeled (User "Sanitizer") $ do 
    i <- asNT unlabel input
    -- i <-  unlabel input
    -- i <- traceShow "relabel" $  unlabel input
    return $ "escaped " ++ i

--timetransitive :: SLIO User Rel String
--timetransitive = do
--    input <- label Input "malicious code"
--    x <- escape input
--    xx <- unlabel x
--    disallowIS
--    traceShow "allowing" allowSD
--    db <- label DB xx
--    xx <- unlabel x
--    unlabel db

timetransitive2 :: StateT (NTTState User) (StateT (SLIOState (Rel User) User) IO) String -- (MonadIFC st Rel User m, MonadNTT nt User m) => m String
timetransitive2 = do
    input <- label (User "Input") "malicious code"
    --xx <- unlabel input
    --x <- relabel input Sanitizer
    x <- escape input
    disallowIS
    allowSD
    unlabel x
    -- db <- toLabeled (User "DB") (unlabel x)
--    xx <- unlabel x
    -- unlabel db

main :: IO ()
main = do
    (r, s) <- runStateT (runStateT timetransitive2 initNTTState) initState 
    print r
    print s

-- instance (MonadIFC st (Rel User)  User m, MonadNTT (NTTState User) User (StateT (NTTState User) m))
--   => MonadIFC st (Rel User) Rel User (StateT (NTTState User) m) where
