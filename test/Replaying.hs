{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Main
  ( main
  ) where

import           Debug.Trace

import           SimpleStLIO

import           Data.List                      ( (\\)
                                                , nub
                                                )
import           Data.Map                       ( empty
                                                , lookup
                                                )
import           SimpleStLIOUtil

newtype User = User String
  deriving (Eq, Show)

newtype Rel = Rel [(User, User)] deriving (Show )

data R l l1 = Rep Int l l1
  deriving (Eq, Show)

instance Replaying (R User) User Rel where
  create src trg i = [Rep i src trg]
  checkR rlab l1 l2 = case Data.Map.lookup (show l1) rlab of
    Nothing           -> False
    --Just (_, True, _) -> False -- TODO:
    Just (_, lbs, l) ->
      sum lbs == s --(filter (\x -> any (\(Rep ii _ _) -> ii == x) l) [0 .. i - 1]) filter out only those that are relabeled as replaying
     where
      s = foldr
        (\(Rep i _ ll2) acc ->
          if ll2 == l2 then (if acc == (-1) then i else acc + i) else acc
        )
        (-1) -- to avoid problems with 0 when the sum if there is nothing is still 0
        l -- this assumes that there is only one unique for each id to ll2

  --inject rl (Rel st) = Rel $ foldr (\(l1,l2) st -> (l1, l2) : st) st rl

instance Label User Rel where
  -- lcurr must be added to have refl of labels not in st
  lrt (Rel st) lcurr rlab lbl1 lbl2 =
    (traceShow (s) (lbl1, lbl2) `elem` s) ||
     --  check that for each id the replaying is allowed
                                             checkR rlab lbl1 lbl2
   where
    r = refl lcurr
    --Rel rst = inject rlab st
    s = reflTransClosure $ nub (st ++ r)



  -- Check if there is any user who may see information
  -- from this user, and could not do before. If yes,
  -- the upper set is increased.
  incUpperSet (Rel oldSt) (Rel newSt) lcurr rlab user =
    let others = [ u | (_, u) <- newSt ]
    in  any
          (\u ->
            not (lrt (Rel oldSt) lcurr rlab user u)
              && lrt (Rel newSt) lcurr rlab user u
          )
          others

initState :: LIOState User Rel (R User)
initState = LIOState
  { lcurr = []
  , scurr = Rel [(User "NSA", User "Military"), (User "NSA", User "Another")]
  , ntlab = []
  , rlab  = Data.Map.empty
  }

disallowNM :: SLIO User Rel (R User) ()
disallowNM = do
  rel <- getState
  let (Rel st) = rel
  setState (Rel $ st \\ [(User "NSA", User "Military")])



replaying :: SLIO User Rel (R User) String
replaying = do
  file1 <- label (User "NSA") "secret"
  file2 <- label (User "NSA") "secret 2"
  file  <- unlabelReplaying file1 [User "Another"]
  file  <- unlabelReplaying file1 [User "Military"] -- what if instead of file1 this is file2 ??
  --lst <- getReplaying
  --file  <- unlabel file1
  mil   <- newLIORef (User "Military") file
  writeLIORef mil ""
  disallowNM
  writeLIORef mil file
  readLIORef mil

-- ______________________

unlabelAsReplaying
  :: (Label l st, Replaying r l st) => Labeled l a -> l -> SLIO l st r a
unlabelAsReplaying ldata nl = do
  d <- relabel ldata nl
  unlabel d

replaying2 :: SLIO User Rel (R User) String
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
