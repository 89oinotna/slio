{-# LANGUAGE MultiParamTypeClasses, DoAndIfThenElse #-}
-- | This module implements the confidential part of the DLM as described in
-- [1]  Myers, Liskov, "Protecting Privacy using the Decentralized Label Mode" 
--      ACM, 1999.
module DLM
  ( Principal
  , Component(..)
  , DLMLabel(..)
  , DLMState(..)
  , DLM
  , runDLM
    -- * Functionality
  , declassify
  , addActsFor
  , delActsFor
  , addAuthority
  , delAuthority
    -- * Re-exporting LIO functionality (not the nicest way?)
  , Labeled
  , label
  , labelOf
  , toLabeled
  , unlabel
  , relabel
  ) where
import SimpleStLIO
import SimpleStLIOUtil (reflTransClosure)

import Data.List (nub, delete)

type Principal  =  String
data Component  =  Component Principal [Principal]  -- Owner and readers.
  deriving (Eq, Show)

newtype DLMLabel  =  DLMLabel [Component]
  deriving (Eq, Show)
data DLMState  =  DLMState { declassifying :: Bool
                           , authority     :: [Principal]
                           , acts_for      :: [(Principal, Principal)]
                           }

instance Label DLMLabel DLMState where
  -- | When we re declassifying any relabelling is allowed. Otherwise, perform
  -- the check as per [1].
  lrt st lcurr (DLMLabel lbl1) (DLMLabel lbl2)  = declassifying st ||
    all (\(Component owner1 readers1) ->
      any (\(Component owner2 readers2) ->
               (owner2 `acts_for_rt` owner1)
            && all (\reader2 ->
                 any (\reader1 -> reader2 `acts_for_rt` reader1
                     ) readers1
                   ) readers2
          ) lbl2
        ) lbl1
   where
    acts_for_rt p1 p2 = (p1, p2) `elem` reflTransClosure (curr lcurr ++ acts_for st)
    --curr ((DLMLabel [Component p px]):xs)= (p,p) : [(pp,pp) | pp <- px] ++ curr xs
    --curr []= []
    curr = foldr (\(DLMLabel [Component p px]) r -> (p,p) : [(pp,pp) | pp <- px] ++ r) []


  -- | When changing the declassification state to True, any flow becomes
  -- possible so the upper set is increased. Otherwise:
  -- Take all principals in the label (owner or reader). The new state should
  -- not increase the upper set in the acts-for hieararchy for any of them.
  incUpperSet oldSt newSt lcurr (DLMLabel lbl)  =
    let lblPrincs = concatMap getAllPrincipals lbl
        princs    = nub $ [e | (e,_) <- (acts_for newSt)] ++ [e | (_,e) <- (acts_for newSt)]
    in (not (declassifying oldSt) && declassifying newSt) ||
       any (\lp ->
         any (\p -> not (p `acts_for_old` lp) && p `acts_for_new` lp
             ) princs
           ) lblPrincs
   where acts_for_old p1 p2 = (p1, p2) `elem` (reflTransClosure (acts_for oldSt))
         acts_for_new p1 p2 = (p1, p2) `elem` (reflTransClosure (acts_for newSt))
         getAllPrincipals (Component o rs) = o:rs

type DLM = SLIO DLMLabel DLMState

-- Exported functions

runDLM :: [(Principal,Principal)] -> [Principal] -> DLM a
       -> IO (a, LIOState DLMLabel DLMState)
runDLM afh auth comp =
  unSLIO comp (LIOState { lcurr = []
                         , scurr = DLMState { declassifying = False
                                            , authority     = auth
                                            , acts_for      = afh
                                            }
                          , ntlab = []
                         }
               )

-- | Declassify a labeled value to the provided target label. The 'authCheckLbl'
-- verifies that the computation has the authority necessary to perform this
-- declassification, as described in [1].
declassify :: Labeled DLMLabel a -> DLMLabel
           -> DLM (Maybe (Labeled DLMLabel a))
declassify lblVal (DLMLabel tgtLbl) = do
  st <- getState
  lcurr <- getLabel
  let authCheckLbl = tgtLbl ++ [Component p [] | p <- authority st]
  let lbl          = labelOf lblVal
  if lrt st lcurr lbl (DLMLabel authCheckLbl) --lcurr???
  then do res <- toLabeled (DLMLabel tgtLbl) $
            do setState (st {declassifying = True})
               unlabel lblVal
          return (Just res)
  else return Nothing

addActsFor :: (Principal, Principal) -> DLM ()
addActsFor rel = do
  st <- getState
  setState (st {acts_for = nub (rel:acts_for st)})

delActsFor :: (Principal, Principal) -> DLM ()
delActsFor rel = do
  st <- getState
  setState (st {acts_for = delete rel (nub (acts_for st))})

addAuthority :: Principal -> DLM ()
addAuthority p = do
  st <- getState
  setState (st {authority = p:authority st})

delAuthority :: Principal -> DLM ()
delAuthority p = do
  st <- getState
  setState (st {authority = delete p (nub (authority st))})
