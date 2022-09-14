{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module DCLabels
  ( -- * Label data structure:
    module DCLabels.Core,
    module DCLabels.DSL,
    DCPriv, privDesc,
    DCState, DCLabeled, DC, noPriv,
    -- * State and restricted modifiers:
    partDowngradeP, canFlowToP,
    unlabelP, labelP, relabelLabeledP,
    -- * LIORef basic interface
    newLIORefP, readLIORefP, writeLIORefP,
    -- * toLabeledP
    toLabeledP,
    -- * Run functionality (so should not use runLIO, but currently not
    -- prevented)
    runDC
  ) where

import SimpleStLIO

-- Imports from DCLabels included in original LIO.
import DCLabels.Core
import DCLabels.TCB
import DCLabels.DSL

import Control.Monad (unless)
import Data.Monoid (Monoid(..))
import qualified Data.Set as Set

type DCState    =  [DCPriv]
type DCLabeled  =  Labeled DCLabel
type DC         =  SLIO DCLabel DCState

instance Label DCLabel DCState where
  -- | /can-flow-to/ relation on labels (taking privileges into account).
  lrt p l1 l2 = 
    let (s1,i1) = (dcSecrecy l1, dcIntegrity l1)
        (s2,i2) = (dcSecrecy l2, dcIntegrity l2)
        pd = foldl dcAnd dcTrue (map privDesc p)
    in (pd `dcAnd` s2) `dcImplies` s1 && (pd `dcAnd` i1) `dcImplies` i2
  incUpperSet oldSt newSt lbl =
    let oldL = downgradeP oldSt lbl bottom
        newL = downgradeP newSt lbl bottom
    in not (lrt [noPriv] oldL newL)


dcImpliesBoth :: DCLabel -> DCLabel -> Bool
dcImpliesBoth l1 l2 =
    (dcSecrecy   l2 `dcImplies` dcSecrecy   l1) &&
    (dcIntegrity l1 `dcImplies` dcIntegrity l2)

-- | The empty privilege, or no privileges, corresponds to logical
-- @True@.
noPriv :: DCPriv
noPriv = DCPrivTCB dcTrue

instance Monoid DCPriv where
  mempty = noPriv
  mappend p1 p2 = mintTCB . dcReduce $!
                   privDesc p1 `dcAnd` privDesc p2



{----------------------------------------}
{-           LIO state changes          -}
{----------------------------------------}

withPrivileges :: [DCPriv] -> DC a -> DC a
withPrivileges p comp = do oldP <- getState
                           setState p
                           x <- comp  
                           setState oldP
                           return x

withPrivilege :: DCPriv -> DC a -> DC a
withPrivilege p = withPrivileges [p]


{----------------------------------------}
{-              LIO run                 -}
{----------------------------------------}

runDC :: DC a -> IO (a, LIOState DCLabel DCState)
runDC comp = 
  unSLIO comp (LIOState { lcurr  =  []
                         , scurr  =  [noPriv]   } )

{----------------------------------------}
{-              P-variants              -}
{----------------------------------------}

partDowngradeP :: DCPriv -> DCLabel -> DCLabel -> DCLabel
partDowngradeP p l1 l2 = downgradeP [p] l1 l2

downgradeP :: [DCPriv] -> DCLabel -> DCLabel -> DCLabel
downgradeP privs la lg =  
    let sa  = dcSecrecy $ la
        ia  = dcIntegrity la
        sg  = dcSecrecy   lg
        ig  = dcIntegrity lg
        sa' = dcFormula . Set.filter (f pd) $ unDCFormula sa
        sr  = if isFalse sa 
                then sa
                else sa' `dcAnd` sg
        ir  = (pd `dcAnd` ia) `dcOr` ig
    in dcLabel sr ir
      where f p c = not $ p `dcImplies` (dcFormula . Set.singleton $ c)
            pd = foldl dcAnd dcTrue (map privDesc privs)

canFlowToP :: DCPriv -> DCLabel -> DCLabel -> Bool
canFlowToP p l1 l2 = lrt [p] l1 l2

bottom :: DCLabel
bottom  = dcLabel dcTrue dcFalse

lub :: DCLabel -> DCLabel -> DCLabel
lub l1 l2 = DCLabel
    { dcSecrecy   = dcReduce $ dcSecrecy l1   `dcAnd` dcSecrecy l2
    , dcIntegrity = dcReduce $ dcIntegrity l1 `dcOr`  dcIntegrity l2 }

-- | To unlabel a value, we perform the unlabelling in a /toLabeled/
-- sub-computation (so as not to taint the PC with the label of the
-- value). The result of /toLabeled/ is a value labelled with the
-- result of the /downgrade/ operation, so as to raise the PC as
-- little as possible. Note that, so far, /v/ is just a relabelling of
-- /x/ to the downgraded label. Finally, the PC is tainted with this
-- label by unlabelling /v/.
unlabelP :: DCPriv -> DCLabeled a -> DC a

unlabelP p x = do curL <- getLabel
                  oldP <- getState
                  setState [p]
                  v <- toLabeled (downgradeP [p] (labelOf x) (foldr lub bottom curL)) $
                       unlabel x
                  setState oldP
                  unlabel v

labelP :: DCPriv -> DCLabel -> a -> DC (DCLabeled a)
labelP p l x = withPrivilege p $ label l x

newLIORefP :: DCPriv -> DCLabel -> a -> DC (LIORef DCLabel a)
newLIORefP p l a = withPrivilege p $ newLIORef l a

-- | Similar to unlabelP
readLIORefP :: DCPriv -> LIORef DCLabel a -> DC a
readLIORefP p lr = 
  do curL <- getLabel
     oldP <- getState
     setState [p]
     v <- toLabeled (downgradeP [p] (labelOfRef lr) (foldr lub bottom curL)) $
          readLIORef lr
     setState oldP
     unlabel v

writeLIORefP :: DCPriv -> LIORef DCLabel a -> a -> DC ()
writeLIORefP p lr a = withPrivilege p $ writeLIORef lr a

toLabeledP p l m = withPrivilege p $ toLabeled l m

relabelLabeledP :: DCPriv -> DCLabel -> DCLabeled a -> DC (Maybe (DCLabeled a))
relabelLabeledP p newl lv = do
  let origl = labelOf lv
  st <- getState
  if (canFlowToP p newl origl && canFlowToP p origl newl) 
    then do  res <- toLabeled newl $ do setState (p:st)
                                        unlabel lv
             return $ Just res
    else return Nothing
