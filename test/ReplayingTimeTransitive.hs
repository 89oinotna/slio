{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Main
  ( main
  ) where

import           Debug.Trace

import           SimpleStLIO

import           Data.List                      ( (\\)
                                                , groupBy
                                                , nub
                                                )
import           Data.Map                       ( elems
                                                , empty
                                                , insert
                                                , lookup
                                                )
import           SimpleStLIOUtil
import Control.Monad (when)

newtype User = User String
  deriving (Eq, Show)

newtype Rel = Rel [(User, User)] deriving (Show )

data Rep l = Rep Int l l
  deriving (Eq, Show)

instance Replaying (Rep) User Rel where
  create src trg i = [Rep i src trg]
  checkR rlab l1 l2 = case Data.Map.lookup (show l1) rlab of
    Nothing          -> False
    Just (_, lbs, l) -> sum lbs == s --(filter (\x -> any (\(Rep ii _ _) -> ii == x) l) [0 .. i - 1]) filter out only those that are relabeled as replaying
     where
      s = foldr
        (\(Rep i _ ll2) acc -> if ll2 == l2 then (if acc == (-1) then i else acc + i) else acc)
        (-1) -- to avoid problems with 0 when the sum if there is nothing is still 0
        l -- this assumes that there is only one unique for each id to ll2

  --inject rl (Rel st) = Rel $ foldr (\(l1,l2) st -> (l1, l2) : st) st rl

instance Label User Rel (Rep) where
  -- lcurr must be added to have refl of labels not in st
  lrt (Rel st) lcurr rlab lbl1 lbl2 =
    (traceShow (show s ++ "nrlab:" ++ show nrlab) (lbl1, lbl2) `elem` s) ||
     --  check that for each id the replaying is allowed
                                             checkR nrlab lbl1 lbl2 -- TODO: reflexive transitive closure on rlab
   where
    r = refl $ lbl1:lbl2:lcurr
    --Rel rst = inject rlab st
    s = reflTransClosure $ nub (st ++ r)
    nrlab = foldr
          (\rels@((Rep _ l1 _) : _) acc ->
            case Data.Map.lookup (show l1) acc of
              Just (i, lst, _) -> Data.Map.insert (show l1) (i, lst, rels) acc
          )
          rlab
        $ groupBy (\(Rep i l1 l2) (Rep ii ll1 ll2) -> l1 == ll1)
        rtr
    rtr = transClosure s $ concatMap (\(_, _, l) -> l) (Data.Map.elems rlab)
    transClosure st rlab =
      -- Perform one step of transitive closure, i.e. if we have both (e1,e2) and
      -- (e2,e3), add (e1,e3).
      let nxs = nub $  rlab ++ [ Rep i l1 e2 | (e1, e2)      <- st , (Rep i l1 l2) <- rlab , l2 == e1 ]
      -- If we found new relations we need to look for more recursively, otherwise
      -- we are done.
      in  if length rlab == length nxs then nxs else transClosure st nxs



  -- Check if there is any user who may see information
  -- from this user, and could not do before. If yes,
  -- the upper set is increased.
  incUpperSet (Rel oldSt) (Rel newSt) lcurr rlab user =
    let others = [ u | (_, u) <- newSt ]
    in  any
          (\u ->
            not (traceShow (lrt (Rel oldSt) lcurr rlab user u) (lrt (Rel oldSt) lcurr rlab user u))
              && traceShow (lrt (Rel newSt) lcurr rlab user u) lrt (Rel newSt) lcurr rlab user u
          )
          others

initState :: LIOState User Rel (Rep)
initState = LIOState { lcurr = []
                     , scurr = Rel [(User "NSA", User "Military")]
                     , ntlab = []
                     , rlab  = Data.Map.empty
                     }

disallowNM :: SLIO User Rel (Rep) ()
disallowNM = do
  rel <- getState
  let (Rel st) = rel
  setState (Rel $ st \\ [(User "NSA", User "Military")])

disallowMB :: SLIO User Rel (Rep) ()
disallowMB = do
  rel <- getState
  let (Rel st) = rel
  setState (Rel $ st \\ [(User "Military", User "Another")])

allowMB :: SLIO User Rel (Rep) ()
allowMB = do
  rel <- getState
  let (Rel st) = rel
  setState (Rel $ st ++ [(User "Military", User "Another")])

allowNM :: SLIO User Rel (Rep) ()
allowNM = do
    rel <- getState
    let (Rel st) = rel
    setState (Rel $ st ++ [(User "NSA", User "Military")])


leak :: SLIO User Rel Rep Integer
leak = do
  file1 <- label (User "NSA") 0
  r <- newLIORef (User "Another") 1

  --file  <- unlabel file1
  --mil   <- newLIORef (User "Military") file
  --writeLIORef mil 1
  _ <- toLabeled (User "NSA") ( do
    
    file  <- unlabelReplaying file1 [User "Military"]
    --disallowNM
    when (file==0) (do
      allowMB
      writeLIORef r 0))
  readLIORef r

main :: IO ()
main = do
  (r, s) <- unSLIO leak initState
  print r
  print s
