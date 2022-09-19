module SimpleStLIOUtil
  ( reflTransClosure
  ) where

import Data.List (nub)

-- | Returns the reflexive and transitive closure of the relations specified in
-- its argument.
reflTransClosure :: Eq a => [(a,a)] -> [(a,a)]
reflTransClosure xs =
  -- All the reflexive relations
  let rxs = [(e,e) | (e,_) <- xs] ++ [(e,e) | (_,e) <- xs]
  in nub $ rxs ++ transClosure xs

-- | Returns the transitive closure of the relations specified in its argument.
transClosure :: Eq a => [(a,a)] -> [(a,a)]
transClosure xs = 
  -- Perform one step of transitive closure, i.e. if we have both (e1,e2) and
  -- (e2,e3), add (e1,e3).
  let nxs = nub $ xs ++ [ (e1, e3) | (e1, e2) <- xs, (x, e3) <- xs, x == e2 ]
  -- If we found new relations we need to look for more recursively, otherwise
  -- we are done.
  in  if (length xs) == (length nxs) then nxs else transClosure nxs
