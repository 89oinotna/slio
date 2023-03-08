{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Debug.Trace

import SimpleStLIO
import SimpleStLIOUtil

import Data.List ((\\))
import SimpleStLIO (newLIORef, writeLIORef, readLIORef, unlabel)
import qualified Data.HashMap.Strict           as HM
import Impl



initState :: LIOState User Rel (Rep)
initState = LIOState
  { lcurr = HM.empty
  , scurr = Rel
              [(User "Other", User "Military"), (User "Military", User "NSA")]
  , ntlab = HM.empty
  , rlab  = Rep HM.fromList [(User "NSA", [(User "NSA", 0, User "Military")])]
  , newid = 0
  }

condAllow :: SLIO User Rel (Rep) String
condAllow = do
    y <- label (User "NSA") "secret"
    x <- newLIORef (User "Military") 1
    _ <- toLabeled (User "NSA") (do
        yy <- asRp unlabel y
        when (yy == 0) (do
            z <- label "Military" yy

            --zz <- unlabel 
        )
        
        
    )

  _ <- toLabeled High $ do
    h <- unlabel highData
    when (h == 0) (setState True >> writeLIORef lowRef 0)
  readLIORef lowRef
  

main :: IO ()
main = do
  (r, s) <- unSLIO condAllow initState
  print r
  print s