module Main (main) where

import DLM
import SimpleStLIO -- Used only for debugging / inspecting!

military, nsa :: Principal
military = "military"
nsa = "nsa"

-- | A principal adds his or her data to the collective document, correctly
-- updating the label on that document. Every principals adds the permission for
-- 'receiver' to read the result.
addInfo :: Principal -> Labeled DLMLabel String -> Principal
        -> DLM (Labeled DLMLabel String)
addInfo me groupDoc receiver = do
  addAuthority me
  myDoc     <-  label (DLMLabel [Component me []]) ("This is "++me++"'s data.")
  let (DLMLabel groupLbl) = labelOf groupDoc
  combined  <-  toLabeled (DLMLabel (Component me []:groupLbl)) $ do
                  myData   <- unlabel myDoc
                  groupData <- unlabel groupDoc
                  return (groupData ++ myData)
  (Just x)  <-  declassify combined (DLMLabel (Component me [receiver]:groupLbl))
  delAuthority me
  return x

-- example :: DLM (String, DLMLabel)
-- example = do
--   collected    <-  label (DLMLabel []) "Collecting group data."
--   collectedB   <-  addInfo bob  collected  dave  -- label is {bob:dave}
--   collectedBC  <-  addInfo carl collectedB dave  -- label is {bob:dave ; carl:dave}

--   -- Relabelling only works if john can act for dave.
--   -- delActsFor (john,dave)
--   result  <-  relabel collectedBC (DLMLabel [Component alice [john]])
--   value   <-  unlabel result
--   return (value, labelOf result)  -- label is {alice:john}

example2 :: DLM (String)
example2 = do
  file    <-  label (DLMLabel [Component military []]) "secret"
  file <- unlabel file
  mil <- label (DLMLabel [Component military []]) "secret"
  return file  

main :: IO ()
main = do
--   ((res,resL), st) <- runDLM [] [] example
  (res, st) <- runDLM [] [] example2
  putStrLn $ "Result:        " ++ show res
  --putStrLn $ "Result-label:  " ++ show resL
  putStrLn $ "Declassifying: " ++ show (declassifying (scurr st))
  putStrLn $ "Authority:     " ++ show (authority     (scurr st))
  putStrLn $ "Acts-for:      " ++ show (acts_for      (scurr st))
