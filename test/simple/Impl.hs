{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}

module Impl where
import           Data.IORef                     ( IORef
                                                , newIORef
                                                , readIORef
                                                , writeIORef
                                                )
import           Debug.Trace

import           SimpleStLIO

import           Control.Monad                  ( when )
import qualified Data.HashMap.Strict           as HM
import           Data.Hashable
import           Data.List                      ( (\\)
                                                , groupBy
                                                , nub
                                                )
import qualified Data.List                     as List
import           Data.Map                       ( elems
                                                , empty
                                                , lookup
                                                )
import           SimpleStLIOUtil

newtype User = User String
  deriving (Eq, Show, Hashable)

newtype Rel = Rel [(User, User)] deriving (Show )

-- data Rep l = Rep Int l l
--   deriving (Eq, Show)

-- newtype Rep l= Rep (HM.HashMap (l, Int) [(l, Bool)]) -- to which labels is replaying
newtype Rep= Rep (HM.HashMap User [(User, Int, User, Bool)]) deriving (Show) -- to which labels is replaying

insert
  :: (Hashable k, Eq a, Eq k)
  => HM.HashMap k [a]
  -> k
  -> [a]
  -> HM.HashMap k [a]
insert m k v = case HM.lookup k m of
  Nothing -> HM.insert k v m
  Just xs -> HM.insert k (nub $ v ++ xs) m


instance Replaying Rep User Rel where
  --addPromises :: l -> Int -> [l] -> SLIO l st r ()
  addPromises l i lst = SLIO
    (\s@(LIOState lcurr st nt assocnt (Rep rl) id) ->
      let genl = List.map (l, i, , False) lst
      in
        let
          nrl = case HM.lookup l rl of
            Nothing -> insert rl l genl
            Just ls -> insert
              rl
              l
              (List.filter (\(l1, i, l2, _) -> (l1, i, l2, True) `notElem` ls)
                           genl
              )
        in 
      --let lst' = List.map (l, i, , False) lst in
            return ((), LIOState lcurr st nt assocnt (Rep nrl) id)
    )


  -- replay everything in lcurr that has a promise for l
  enableRP l = SLIO
    (\s@(LIOState lcurr st nt assocnt (Rep rl) id) ->
      let ls = HM.keys lcurr
      in
        let
          nrl = HM.mapMaybeWithKey
            (\k lst -> Just
              (List.map
                (\v@(l1, i, l2, b) ->
                  if l2 == l && l1 `elem` ls then (l1, i, l2, True) else v
                )
                lst
              )
            )
            rl
        in  traceShow ("post" ++ show nrl)
                      return
                      ((), LIOState lcurr st nt assocnt (Rep nrl) id)
    )

  disableRP l i = SLIO
    (\s@(LIOState lcurr st nt assocnt (Rep rl) id) ->
      let
        newrl =
          (HM.mapMaybeWithKey
              -- (\k lst -> Just (List.map (\v@(l1, i1, l2, b)-> if l1 == l && i == i1 then (l1,i1,l2, False) else v) lst))
            (\k lst -> Just
              (List.filter (\v@(l1, i1, l2, b) -> l1 /= l && i /= i1) lst)
            )
            rl
          )
      in  traceShow ("post" ++ show newrl)
                    return
                    ((), LIOState lcurr st nt assocnt (Rep newrl) id)
    )


instance Label User Rel Rep where
  -- lcurr must be added to have refl of labels not in st
  lrt (Rel st) lcurr (Rep rl) lbl1 lbl2 =
    (traceShow (show s ++ "nrlab:" ++ show nrlab) (lbl1, lbl2) `elem` s)
      ||
     --  check that for each id the replaying is allowed
         checkRep
   where
    r = refl $ HM.keys lcurr
    --Rel rst = inject rlab st
    s = reflTransClosure $ nub (st ++ r)
    transClosure st rlab =
      -- Perform one step of transitive closure, i.e. if we have both (e1,e2) and
      -- (e2,e3), add (e1,e3).
      let nxs =
            nub
              $  rlab
              ++ [ (l1, i, e2, True)
                 | (e1, e2)          <- st
                 , (l1, i, l2, True) <- rlab
                 , l2 == e1
                 ]
      -- transitive using rlab
              ++ [ (l1, i, ll2, True)
                 | (l1 , i , l2 , True) <- rlab
                 , (ll1, ii, ll2, True) <- rlab
                 , l2 == ll1 && i == ii
                 ]
      -- If we found new relations we need to look for more recursively, otherwise
      -- we are done.
      in  if length rlab == length nxs then nxs else transClosure st nxs
    rtr      = transClosure s (concat $ HM.elems rl)
        -- $ concatMap (\(_, _, l) -> l) (Data.Map.elems rlab)
    nrlab    = HM.fromListWith (++) $ map (\e@(l, i, l2, b) -> (l, [e])) rtr
    checkRep = case HM.lookup lbl1 nrlab of
      Nothing    -> False
      Just rplTo -> case HM.lookup lbl1 lcurr of
        Nothing  -> False
        Just lst -> all (\i -> (lbl1, i, lbl2, True) `elem` rplTo) lst --for all the ids there is the flow

  -- Check if there is any user who may see information
  -- from this user, and could not do before. If yes,
  -- the upper set is increased.
  incUpperSet (Rel oldSt) (Rel newSt) lcurr rlab rlab' user =
    let others = [ u | (_, u) <- newSt ]
    in  any
          (\u ->
            not
                (traceShow ("not" ++ show user ++ show u)--(lrt (Rel oldSt) lcurr rlab user u)
                           (lrt (Rel oldSt) lcurr rlab user u)
                )
              && traceShow
                   ("and" ++ show user ++ show u)--(lrt (Rel newSt) lcurr rlab user u)
                   lrt
                   (Rel newSt)
                   lcurr
                   rlab'
                   user
                   u
          )
          others
