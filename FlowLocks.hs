{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
-- | This module implements the flow locks policy language as defined in the
-- paper "Paragon for Practical Programming with Information-Flow Control" by
-- Broberg, van Delft and Sands, Springer 2013.
module FlowLocks
  ( FLPolicy(..)
  , FLClause
  , FLLock
  , FLLockSet
  , FLLIO
  , Actor
  , ActorSetRep(..)
  , LockID
  , FLGlobalPolicy
  , FLAtom
  , FLLabeled
  -- * operations
  , mkActor
  , mkLockID
  , openLock
  , closeLock
  , isLockOpen
  , addGlobalClause
  , setGlobalPolicy
  -- * Run
  , runFSLIO
  ) where

import SimpleStLIO

-- We use the flow locks framework.
import Security.InfoFlow.Policy.FlowLocks as FlowLocks
import qualified Security.InfoFlow.Policy.FlowLocks.Datalog as Datalog

import Control.Applicative (Applicative(..))
import Control.Monad (ap)
import Data.List ((\\), nub, delete)
import Data.Maybe (catMaybes) 
import Data.Typeable

-- We need an identity monad for running the LRT check in the flow locks
-- framework.

newtype Identity a = Identity { runIdentity :: a }

instance Functor Identity where
    fmap f m = Identity (f (runIdentity m))

instance Monad Identity where
    return a = Identity a
    m >>= k  = k (runIdentity m)

instance Applicative Identity where
    pure = return
    (<*>) = ap

-- * Actors

data Actor = Actor String
  deriving (Eq, Ord, Show, Typeable)

instance ActorId Actor where
  mayEq = (==)

-- | In Paralocks, an actor representation can either mention a concrete actor,
--  or be a quantified variable representing any actor. We also include a
-- distinguished 'top' element, which is one of the requirements (must form a
-- join semi-lattice).
data ActorSetRep aid
    = SingletonActor aid
    | AnyActor
    | NoActor
  deriving (Eq, Ord, Show, Typeable)

instance (ActorId aid) => PartialOrder (ActorSetRep aid) where
    AnyActor `leq` _ = return True
    SingletonActor aid1 `leq` SingletonActor aid2 = return $
        aid1 == aid2
    _ `leq` NoActor = return True
    _ `leq` _ = return False


instance (ActorId aid) => JoinSemiLattice (ActorSetRep aid) where
    top = NoActor

    NoActor `lub` _ = return NoActor
    _ `lub` NoActor = return NoActor

    AnyActor `lub` a = return a
    a `lub` AnyActor = return a

    SingletonActor aid1 `lub` SingletonActor aid2
                       | aid1 == aid2 = return $ SingletonActor aid1
                       | otherwise    = return NoActor

instance (ActorId aid) => Lattice (ActorSetRep aid) where
    bottom = AnyActor

    NoActor `glb` a = return a
    a `glb` NoActor = return a

    AnyActor `glb` _a = return AnyActor
    _a `glb` AnyActor = return AnyActor

    SingletonActor aid1 `glb` SingletonActor aid2
                       | aid1 == aid2 = return $ SingletonActor aid1
                       | otherwise    = return AnyActor


instance ActorSet (ActorSetRep Actor) Actor where
  inSet aid1 (SingletonActor aid2) = return $ aid1 == aid2
  inSet _aid AnyActor = return True
  inSet _aid NoActor  = return False

  enumSetMembers (SingletonActor aid) = return $ Just [aid]
  enumSetMembers AnyActor = return Nothing
  enumSetMembers NoActor  = return $ Just []
  
-- * Locks

data LockID  = LockID String
  deriving (Eq, Ord, Show, Typeable)

type FLLock    = Lock    LockID Actor
type FLLockSet = LockSet LockID Actor

-- * Policies

type FLPolicy       = Policy       LockID (ActorSetRep Actor)
type FLGlobalPolicy = GlobalPolicy LockID (ActorSetRep Actor)
type FLAtom         = Atom         LockID
type FLClause       = Clause       LockID (ActorSetRep Actor)

data FLState = FLState { lockState :: FLLockSet
                       , globalPol :: FLGlobalPolicy
                       , counter   :: Integer
                       }

type FLLabeled = Labeled FLPolicy
type FLLIO = SLIO FLPolicy FLState

instance Label FLPolicy FLState where
  lrt st lbl1 lbl2 = 
    let (LockSet ls) = lockState st
    in runIdentity (FlowLocks.lrt (globalPol st) ls lbl1 lbl2)
  -- | We get all locks that can be derived to be open in both the old and the
  -- new state. We then specialize the label to each set. That is, we get a new
  -- label back which allows the same flows whether the provided locks are
  -- closed or open (it acts as if the locks are always open).
  -- Then, we increase the upper set iff the specialised label for the old locks
  -- is strictly more restrictive than the specialised label for the new locks
  incUpperSet oldSt newSt (Policy lbl) =
    let (LockSet oldOpen) = deriveAllLocks (globalPol oldSt) (lockState oldSt)
        (LockSet newOpen) = deriveAllLocks (globalPol newSt) (lockState newSt)
    in not $ runIdentity (FlowLocks.lrt [] [] (Policy $ specialize lbl oldOpen) 
                                              (Policy $ specialize lbl newOpen))

-- | Specialize a policy to a lock state
specialize :: [FLClause] -> [Lock LockID Actor] -> [FLClause]
specialize cls ls =
  let ncls = nub $ cls ++ concatMap downgradeOnce cls
  in  if (length ncls == length cls)
        then cls                -- Nothing new derived
        else specialize ncls ls -- Find more
  where
   -- | For each atom in the clause body, find all locks that this atom could be
   -- mapped to in the current lock state. Remove the atom and substitute 
   -- accordingly.
   -- Returns possibly empty list of clauses that are equivalent to the given
   -- clause in the current lock state, with one atom less in the body.
   downgradeOnce :: FLClause -> [FLClause]
   downgradeOnce (Clause hd aset b) =
     concatMap (\a ->
       let ss = findSubst hd aset a
       in  map (\s ->
             let h' = substHead s hd
                 b' = delete a b
                 a' = subst s aset
             in  Clause h' a' b'
           ) ss
     ) b

   -- | Return the list of substitutions that transform the atom into a lock
   -- that is in the current lock state.
   findSubst :: ActorSetRep Actor -> [ActorSetRep Actor] 
             -> Atom LockID -> [[(ActorRep, Actor)]]
   findSubst hset aset (Atom lockId arg) = catMaybes $ 
     map (\(Lock lockId' arg') ->
       if lockId == lockId' &&                      -- ^ Same predicate
          length arg == length arg' &&              -- ^ Same arity
          (and $ map constantEqual (zip arg arg'))  -- ^ Not changing constants
         then let f = filter isConstant (zip arg arg')
              in  if varMapsSame f           -- ^ All vars map to same constant
                    then Just f
                    else Nothing
         else Nothing
     ) ls
    where
     constantEqual :: (ActorRep, Actor) -> Bool
     constantEqual (a,b) = case toSet a of
                             AnyActor         -> True
                             SingletonActor x -> x == b
                             _                -> error "Cannot have no actor"
     isConstant :: (ActorRep, Actor) -> Bool
     isConstant (a,_) = toSet a == AnyActor
     toSet :: ActorRep -> ActorSetRep Actor
     toSet HeadActor      = hset
     toSet (QuantActor i) = aset !! i
     varMapsSame :: [(ActorRep, Actor)] -> Bool
     varMapsSame sub = all (\(x,y) ->
                         all (\(x',y') ->
                           if x == x' then y == y' else True
                         ) sub
                       ) sub


   substHead :: [(ActorRep, Actor)]
             -> ActorSetRep Actor -> ActorSetRep Actor
   substHead s h = case lookup HeadActor s of
                     Nothing -> h
                     Just a  -> SingletonActor a

   subst :: [(ActorRep, Actor)] 
         -> [ActorSetRep Actor] -> [ActorSetRep Actor]
   subst s aset = map (\(a,i) -> 
                    case lookup (QuantActor i) s of
                      Nothing -> a
                      Just x  -> SingletonActor x
                  ) (zip aset [0..])

-- | Derive all locks currently open using clauses in the global policy
deriveAllLocks :: FLGlobalPolicy -> FLLockSet -> FLLockSet
deriveAllLocks gpol ls = 
  let gpolD = convertToDLPol gpol
      lsD   = convertToDLDB ls
      nlsD  = Datalog.deriveAll gpolD lsD
  in convertToLS nlsD
  where
    convertToDLPol :: FLGlobalPolicy -> [Datalog.Clause LockID Actor]
    convertToDLPol gp = 
      map (\(DatalogClause sets hd tl) -> 
              Datalog.Clause (predToAtom sets hd) (map (predToAtom sets) tl)
          ) gp
    
    convertToDLDB :: FLLockSet -> [Datalog.Fact LockID Actor]
    convertToDLDB (LockSet l) = map lockToFact l
    convertToDLDB _ = error "No NoSet expected as lockset"
    
    lockToFact :: Lock LockID Actor -> Datalog.Fact LockID Actor
    lockToFact (Lock lockID acts) = Datalog.Fact lockID (map Datalog.Constant acts)
    
    convertToLS :: [Datalog.Fact LockID Actor] -> FLLockSet
    convertToLS db = LockSet (map factToLock db)
    
    factToLock :: Datalog.Fact LockID Actor -> Lock LockID Actor
    factToLock (Datalog.Fact lockID cst) = 
      Lock lockID (map (\(Datalog.Constant i) -> i) cst)
    
    predToAtom :: [ActorSetRep Actor] -> Predicate LockID 
               -> Datalog.Atom LockID Actor
    predToAtom sets (AtomPred (Atom lockID acts)) = 
      Datalog.Atom lockID (map (varToSet sets) acts)
    predToAtom _ _ = error "Cannot have flow predicate in global policy"
    
    varToSet :: [ActorSetRep Actor] -> ActorRep -> Datalog.Argument Actor
    varToSet sets (QuantActor i) = 
      case sets !! i of
        SingletonActor a -> Datalog.ConstantArg (Datalog.Constant a)
        AnyActor         -> Datalog.Variable i
        _                -> error "unknown argument to lock"
    varToSet _ _ = error "No head actors in global pol expected"

-- * Exported functions

mkActor :: String -> FLLIO Actor
mkActor name = do
  st <- getState
  let c = counter st
  let act = Actor (name ++ (show c))
  setState (st {counter = c + 1})
  return act

mkLockID :: String -> FLLIO LockID
mkLockID name = do
  st <- getState
  let c = counter st
  let lockid = LockID (name ++ (show c))
  setState (st {counter = c + 1})
  return lockid

openLock :: FLLock -> FLLIO ()
openLock lock = do
  st <- getState
  let (LockSet ls) = lockState st
  setState (st { lockState = LockSet (nub $ lock:ls) } )

closeLock :: FLLock -> FLLIO ()
closeLock lock = do
  st <- getState
  let (LockSet ls) = lockState st
  setState (st { lockState = LockSet (delete lock ls) } )

isLockOpen :: FLLock -> FLLIO Bool
isLockOpen lock = do
  st <- getState
  let (LockSet ls) = lockState st
  return $ lock `elem` ls

addGlobalClause :: DatalogClause LockID (ActorSetRep Actor) -> FLLIO ()
addGlobalClause clause = do
  st <- getState
  let gp = globalPol st
  setState (st {globalPol = nub $ clause : gp } )

setGlobalPolicy :: FLGlobalPolicy -> FLLIO ()
setGlobalPolicy gp = do
  st <- getState
  setState (st {globalPol = gp} )

-- *  Run FS computations

runFSLIO :: FLGlobalPolicy -> FLLIO a
         -> IO (a, LIOState FLPolicy FLState)
runFSLIO gp comp =
  unSLIO comp (LIOState { lcurr = []
                         , scurr = FLState { lockState = LockSet []
                                           , globalPol = gp
                                           , counter   = 0 } } )  
