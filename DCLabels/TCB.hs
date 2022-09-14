{-# LANGUAGE DeriveDataTypeable #-}
module DCLabels.TCB where

import DCLabels.Core
import Data.Typeable (Typeable)

{----------------------------------------}
{-        Trusted Priv constructor      -}
{----------------------------------------}

-- some types and naming for backwards compatibility with DCLabels systems

newtype DCPriv = DCPrivTCB { privDesc :: Component}
  deriving (Eq, Show, Typeable)

type DCPrivDesc = Component

mintTCB :: Component -> DCPriv
mintTCB = DCPrivTCB

allPrivTCB :: DCPriv
allPrivTCB = DCPrivTCB dcFalse
