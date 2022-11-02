{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}

module Main
  ( main
  ) where

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
newtype Rep l= Rep (HM.HashMap l [(l, Int, l, Bool)]) deriving (Show) -- to which labels is replaying

insert :: (Hashable k, Eq a, Eq k) => HM.HashMap k [a] -> k -> [a] -> HM.HashMap k [a]
insert m k v = case HM.lookup k m of
  Nothing -> HM.insert k v m
  Just xs -> HM.insert k (nub $ v ++ xs) m


instance Replaying Rep User Rel where
  --addPromises :: l -> Int -> [l] -> SLIO l st r ()
  addPromises l i lst = SLIO
    (\s@(LIOState lcurr st nt (Rep rl) id) ->
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
            return ((), LIOState lcurr st nt (Rep nrl) id)
    )


  --replayTo :: l -> SLIO l st r ()
  replayTo l = SLIO
    (\s@(LIOState lcurr st nt (Rep rl) id) ->
      let ls = HM.keys lcurr in  
      let nrl = HM.mapMaybeWithKey
                (\k lst -> Just (List.map (\v@(l1, i, l2, b)-> if l2 == l && l1 `elem` ls then (l1,i,l2, True) else v) lst))
                rl
          in  traceShow ("post"++show nrl) return ((), LIOState lcurr st nt (Rep nrl) id)

    )

  -- rid (Rep id l1 l2) =id
  -- trg (Rep _ _ l2) = l2
  -- create src trg i = [Rep i src trg]
  -- checkRep rlab l1 l2 = case Data.Map.lookup (show l1) rlab of
  --   Nothing          -> False
  --   Just (_, lbs, l) -> sum lbs == s --(filter (\x -> any (\(Rep ii _ _) -> ii == x) l) [0 .. i - 1]) filter out only those that are relabeled as replaying
  --    where
  --     s = foldr
  --       (\(Rep i _ ll2, b) acc -> if b && ll2 == l2 then (if acc == (-1) then i else acc + i) else acc)
  --       (-1) -- to avoid problems with 0 when the sum if there is nothing is still 0
  --       l -- this assumes that there is only one unique for each id to ll2

  --inject rl (Rel st) = Rel $ foldr (\(l1,l2) st -> (l1, l2) : st) st rl

instance Label User Rel Rep where
  -- lcurr must be added to have refl of labels not in st
  lrt (Rel st) lcurr (Rep rl) lbl1 lbl2 = (traceShow (show s ++ "nrlab:" ++ show nrlab)
                                           (lbl1, lbl2) `elem` s) ||
     --  check that for each id the replaying is allowed
                                                                     checkRep
   where
    r   = refl $ HM.keys lcurr
    --Rel rst = inject rlab st
    s   = reflTransClosure $ nub (st ++ r)
    transClosure st rlab =
      --let rlab = filter snd rlab in
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
    rtr = transClosure s (concat $ HM.elems rl)
        -- $ concatMap (\(_, _, l) -> l) (Data.Map.elems rlab)
    nrlab    = HM.fromListWith (++) $ map (\e@(l, i, l2, b) -> (l, [e])) rtr
    -- nrlab = foldr
    --       (\rels@((Rep _ l1 _, _) : _) acc ->
    --         case Data.Map.lookup (show l1) acc of
    --           Just (i, lst, _) -> Data.Map.insert (show l1) (i, lst, rels) acc
    --       )
    --       rlab
    --     $ groupBy (\(Rep i l1 l2, _) (Rep ii ll1 ll2, _) -> l1 == ll1)
    --     rtr
    checkRep = case HM.lookup lbl1 nrlab of
      Nothing -> False
      Just rplTo -> case HM.lookup lbl1 lcurr of
            Nothing  -> False
            Just lst -> all (\i -> (lbl1, i, lbl2, True) `elem` rplTo) lst --for all the ids there is the flow
      --(filter (\x -> any (\(Rep ii _ _) -> ii == x) l) [0 .. i - 1]) filter out only those that are relabeled as replaying
           -- == foldr
              --      (\(_, i, l2, True) acc -> if lbl2 == l2
              --        then (if acc == (-1) then i else acc + i)
              --        else acc
              --      )
              --      (-1) -- to avoid problems with 0 when the sum if there is nothing is still 0
              --      rplTo -- this assumes that there is only one unique for each id to ll2



  -- Check if there is any user who may see information
  -- from this user, and could not do before. If yes,
  -- the upper set is increased.
  incUpperSet (Rel oldSt) (Rel newSt) lcurr rlab rlab' user =
    let others = [ u | (_, u) <- newSt ]
    in  any
          (\u ->
            not
                (traceShow ("not"++show user++show u)--(lrt (Rel oldSt) lcurr rlab user u)
                           (lrt (Rel oldSt) lcurr rlab user u)
                )
              && traceShow ("and"++show user++show u)--(lrt (Rel newSt) lcurr rlab user u)
                           lrt
                           (Rel newSt)
                           lcurr
                           rlab'
                           user
                           u
          )
          others

initState :: LIOState User Rel (Rep)
initState = LIOState
  { lcurr = HM.empty
  , scurr = Rel
              [(User "NSA", User "Military"), (User "Military", User "Another")]
  , ntlab = HM.empty
  , rlab  = Rep HM.empty
  , newid = 0
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
  --file  <- unlabelReplaying file1 [User "Military"] -- what if instead of file1 this is file2 ??
  file <- asReplaying [User "Military"] unlabel file1
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
