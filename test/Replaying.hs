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
  rid (Rep id l1 l2) =id
  trg (Rep _ _ l2) = l2
  create src trg i = [Rep i src trg]
  checkR rlab l1 l2 = case Data.Map.lookup (show l1) rlab of
    Nothing          -> False
    Just (_, lbs, l) -> sum lbs == s --(filter (\x -> any (\(Rep ii _ _) -> ii == x) l) [0 .. i - 1]) filter out only those that are relabeled as replaying
     where
      s = foldr
        (\(Rep i _ ll2, b) acc -> if b && ll2 == l2 then (if acc == (-1) then i else acc + i) else acc)
        (-1) -- to avoid problems with 0 when the sum if there is nothing is still 0
        l -- this assumes that there is only one unique for each id to ll2

  --inject rl (Rel st) = Rel $ foldr (\(l1,l2) st -> (l1, l2) : st) st rl

instance Label User Rel (Rep) where
  -- lcurr must be added to have refl of labels not in st
  lrt (Rel st) lcurr rlab lbl1 lbl2 =
    (traceShow (show s ++ "nrlab:" ++ show nrlab) (lbl1, lbl2) `elem` s) ||
     --  check that for each id the replaying is allowed
                                             checkR nrlab lbl1 lbl2
   where
    r = refl $ lbl1:lbl2:lcurr -- TODO: find an example where is useful that lbl1 and lbl2 are inserted there
    --Rel rst = inject rlab st
    s = reflTransClosure $ nub (st ++ r)
    rtr = transClosure s
        $ concatMap (\(_, _, l) -> l) (Data.Map.elems rlab)
    transClosure st rlab =
      --let rlab = filter snd rlab in
      -- Perform one step of transitive closure, i.e. if we have both (e1,e2) and
      -- (e2,e3), add (e1,e3).
      let nxs = nub $  rlab ++ [ (Rep i l1 e2, True) | (e1, e2)      <- st , (Rep i l1 l2, True) <- rlab , l2 == e1 ]
      -- If we found new relations we need to look for more recursively, otherwise
      -- we are done.
      in  if length rlab == length nxs then nxs else transClosure st nxs
    nrlab = foldr
          (\rels@((Rep _ l1 _, _) : _) acc ->
            case Data.Map.lookup (show l1) acc of
              Just (i, lst, _) -> Data.Map.insert (show l1) (i, lst, rels) acc
          )
          rlab
        $ groupBy (\(Rep i l1 l2, _) (Rep ii ll1 ll2, _) -> l1 == ll1)
        rtr



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
initState = LIOState
  { lcurr = []
  , scurr = Rel [(User "NSA", User "Military"), (User "Military", User "Another")]
  , ntlab = []
  , rlab  = Data.Map.empty
  }

disallowNM :: SLIO User Rel (Rep) ()
disallowNM = do
  rel <- getState
  let (Rel st) = rel
  setState (Rel $ st \\ [(User "NSA", User "Military")])



replaying :: SLIO User Rel (Rep) String
replaying = do
  file1 <- label (User "NSA") "secret"
  --file2 <- label (User "NSA") "secret 2"
  --file  <- unlabelReplaying file1 [User "Another"]
  file  <- unlabelReplaying file1 [User "Military"] -- what if instead of file1 this is file2 ??
  --lst <- getReplaying
  --file  <- unlabel file1
  mil   <- newLIORef (User "Military") file
  --writeLIORef mil ""
  disallowNM
  writeLIORef mil ""
  --mil   <- newLIORef (User "Military") file
  -- mil   <- newLIORef (User "Another") $ file++"A"
  --writeLIORef mil file
  readLIORef mil

-- ______________________
-- This example shows why using relable is not the correct solution

unlabelAsReplaying
  :: (Label l st r, Replaying r l st) => Labeled l a -> l -> SLIO l st r a
unlabelAsReplaying ldata nl = do
  d <- relabel ldata nl
  unlabel d

replaying2 :: SLIO User Rel (Rep) String
replaying2 = do
  file <- label (User "NSA") "secret"
  file <- unlabelAsReplaying file (User "Military") --wrong
  --file <- unlabel file
  mil  <- newLIORef (User "Military") file
  an   <- newLIORef (User "Another") file
  writeLIORef mil ""
  --disallowNM
  writeLIORef mil file
  readLIORef mil
-- ______________________

main :: IO ()
main = do
  (r, s) <- unSLIO replaying initState
  print r
  print s
