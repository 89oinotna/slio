{-# LANGUAGE MultiParamTypeClasses #-}
-- | This module demonstrates how Stateful LIO can be used with a simple dynamic
-- lattice. The modelled hierarchy change is that Alice leaves the company and
-- Bob and Dave get promoted accordingly:
--      Alice                  Bob
--     ^    ^                 ^   ^
--   Bob     Carl   -->   Dave    Carl
--     ^    ^
--      Dave              Alice  (no relation to any other user)
module Main where

import SimpleStLIO
import SimpleStLIOUtil

import Data.List ((\\))

data User = Alice | Bob | Carl | Dave
  deriving (Eq)
  
data Rel = Rel [(User,User)]

instance Label User Rel where
  lrt (Rel st) lbl1 lbl2  =  (lbl1,lbl2) `elem` reflTransClosure st
  -- Check if there is any user who may see information
  -- from this user, and could not do before. If yes,
  -- the upper set is increased.
  incUpperSet (Rel oldSt) (Rel newSt) user = 
    let others = [u | (_,u) <- newSt]
    in any (\u -> not (lrt (Rel oldSt) user u) && 
                      (lrt (Rel newSt) user u)
           ) others

initState :: LIOState User Rel
initState = LIOState { lcurr = []
                     , scurr = Rel [(Dave,Bob),(Dave,Carl),(Bob,Alice),(Carl,Alice)]
                     }

reportTo :: Labeled User a -> LIORef User a -> SLIO User Rel ()
reportTo lblInfo tgt = do
  _ <- toLabeled (labelOf lblInfo) $ do
    info <- unlabel lblInfo
    writeLIORef tgt info
  return ()

aliceLeaves :: SLIO User Rel ()
aliceLeaves = do
  rel <- getState
  let (Rel st) = rel
  setState ( Rel $ (Carl,Bob) : (st \\ [(Bob,Alice),(Carl,Alice),(Dave,Carl)]) )

interfering :: SLIO User Rel ()
interfering = do
  -- sources:
  infoCarl   <-  label Carl "Carl's information"
  -- sinks:
  aliceFile  <-  newLIORef Alice ""
  bobFile    <-  newLIORef Bob   ""
  -- information flows:
  reportTo infoCarl aliceFile
  aliceLeaves
  reportTo infoCarl bobFile
  reportTo infoCarl aliceFile  -- Violation detected.

main :: IO ()
main = do
  (r, s) <- unSLIO interfering initState
  putStrLn $ "Result:        " ++ show r