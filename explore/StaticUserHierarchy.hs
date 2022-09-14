{-# LANGUAGE MultiParamTypeClasses #-}
-- | This module demonstrates how Stateful LIO can be used with a simple static
-- lattice. The modelled hierarchy is:
--      Alice
--     ^    ^
--   Bob     Carl
--     ^    ^
--      Dave
module StaticUserHierarchy where

import SimpleStLIO

data User = Alice | Bob | Carl | Dave
  deriving (Eq)
instance Label User () where
  lrt _ _    Alice  =  True
  lrt _ Dave _      =  True
  lrt _ lbl1 lbl2   =  lbl1 == lbl2
  -- | Should never be called:
  incUpperSet _ _ _ =  False 

initState :: LIOState User ()
initState = LIOState { lcurr = [], scurr = () }

reportTo :: Labeled User a -> LIORef User a -> SLIO User () ()
reportTo lblInfo tgt = do
  _ <- toLabeled (labelOf lblInfo) $ do
    info <- unlabel lblInfo
    writeLIORef tgt info
  return ()

interfering :: SLIO User () ()
interfering = do
  -- sources:
  infoCarl   <-  label Carl "Carl's information"
  -- sinks:
  aliceFile  <-  newLIORef Alice ""
  bobFile    <-  newLIORef Bob   ""
  -- information flows:
  reportTo infoCarl aliceFile
  reportTo infoCarl bobFile    -- Violation detected.
