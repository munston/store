{-# Language OverlappingInstances,IncoherentInstances,UndecidableSuperClasses,RankNTypes,TypeFamilies , FlexibleContexts , UndecidableInstances , GADTs , FlexibleInstances , MultiParamTypeClasses , TypeOperators , ConstraintKinds , ScopedTypeVariables , TypeApplications , KindSignatures , DataKinds , AllowAmbiguousTypes#-}
module Carrage where

import GHC.Exts
import Store
import Nat
import Lib.Parametric
import Data.Proxy
import Data.Type.Equality (type (==))

---
-- Indexed

data Indexed (n::Nat) a = Indexed a

getIndex :: forall n a. FromNat n => Indexed n a -> Int
getIndex _ = fromNat @n

instance Functor (Indexed n) where
 fmap f (Indexed a) = Indexed (f a)

instance Load a => Load (Indexed n a) where
 decode xs = let n = read @Int (takeWhile (/= ':') xs) in (Indexed $ decode (tail (dropWhile (/=':') xs)))

instance (FromNat n,Save a) => Save (Indexed n a) where
 encode (Indexed a) = (show $ fromNat @n) ++ ":" ++ encode a

-- central constraint
type Index n a = (FromNat n,Store a) 

instance Index n a => Store (Indexed n a) where
 storeName = storeName @a ++ "." ++ (show $ fromNat @n)
 storeInitialization = Indexed (storeInitialization @a)

---
-- Indicies

data Indicies (ns::[Nat]) a where
 EmptyIndicies :: Indicies '[] a
 ConsIndicies :: (FromNat n,Store a,Parametric a init) => Indexed n a -> (Indicies ns a) -> Indicies (n ': ns) a

class UpdateIndicies ns a where
 updateIndicies :: [[Double]] -> Indicies ns a -> IO (Indicies ns a)

instance UpdateIndicies '[] a where
 updateIndicies [] EmptyIndicies = return EmptyIndicies

instance UpdateIndicies ns a => UpdateIndicies (n ': ns) a where
 updateIndicies (y:ys) (ConsIndicies (Indexed a) xs) = do
  let a' = reparametrize y a
  xs' <- updateIndicies ys xs
  return $ ConsIndicies (Indexed a') xs'

class SaveIndicies ns a where
 saveIndicies :: Indicies ns a -> IO ()

instance SaveIndicies '[] a where
 saveIndicies EmptyIndicies  = return ()

instance SaveIndicies ns a => SaveIndicies (n ': ns) a where
 saveIndicies (ConsIndicies a xs) = writeNextStore a >> saveIndicies xs

class LoadIndicies (ns :: [Nat]) a where
 loadIndicies :: IO (Indicies ns a)

instance LoadIndicies '[] a where
 loadIndicies = return EmptyIndicies

instance (Store a,LoadIndicies ns a,FromNat n,Parametric a init) => LoadIndicies (n ': ns) a where
 loadIndicies = do
  x <- lastStore @(Indexed n a)  
  xs <- loadIndicies @ns @a
  return (ConsIndicies x xs)


{-
a carrage has a start index
and a length
both stored at type level as phantom Nats

it has a populate function
which uses the store instance over the contents, 
in an Indexed wrapper, to consme a type level list of Nats
and return the full carrage

as it opperates over a store, 
it can delete the contents and read it back in again
this is *slow*, but easy to implement.
(buffering at type level is a pain!)
-}

type family Nexts (n :: Nat) (m :: Nat) :: [Nat] where
 Nexts n Z = '[]
 Nexts n (S m) = n ': Nexts (S n) m

data Carrage (start::Nat) (cursor::Nat) (length::Nat) (end::Nat) a = Carrage (Indicies (Nexts cursor length) a)

--saveCarrage :: Carrage start cursor length end a  -> IO ()
-- updateIndicies :: (a -> IO a) -> Indicies ns a -> IO (Indicies ns a)
editCarrage :: UpdateIndicies (Nexts cursor length) a => [[Double]] -> Carrage start cursor length end a -> IO (Carrage start cursor length end a )
editCarrage f (Carrage xs) = updateIndicies f xs >>= return . Carrage 
-- note editCarrage and updateIndicies are both inadiqate for learning!
-- the functor modification is no good for the simultaious support.



loadCarrage :: forall start cursor length end a ns. (LoadIndicies (Nexts cursor length) a,ns ~ IO (Carrage (start::Nat) (cursor::Nat) (length::Nat) (end::Nat) a)) => IO (Carrage start cursor length end a )
loadCarrage = loadIndicies @(Nexts cursor length) >>= return . Carrage

saveCarrage :: SaveIndicies (Nexts cursor length) a => Carrage start cursor length end a  -> IO ()
saveCarrage (Carrage xs) = saveIndicies xs


-- carrage has 2 modes of opperation, differing in terms of
-- if the start index is incrameted or not
-- between a sequence of modifications on the Carrage
-- during which the entries are saved after the modification is enacted.
--
-- proposals are made for the parameter updates
-- the winner is found, and the update applied, and the carrage saved
-- a new carrage with incramented start is loaded, and the process starts over.
-- a learning routine is used to produce the parameters for the update.
--
-- the way this is implemented, is to have the routine which can access the container
-- to make the modifications and test the new action against the loss, in selecting the update.
-- as long as it returns the final selected update paramters, it should work
-- this means, it should require a function that uses the ensemble, and returns IO [[Double]]
-- note that the carrage itself may only form part of the container that the loss opperates on
-- this means that the container should first be modified, and then the new container (carrage)
-- used to edit the overall object so that the loss can be run on it during the learning run.
--
-- Carrage s l a -> IO [[Double]]
-- this is the type of the function which awaits the Carrage, and returns the proposed update.
-- this can be called an "update returning function", or a "proposal selector"

type Constr (c::Nat) (l::Nat) a = (SaveIndicies (Nexts c l) a,UpdateIndicies (Nexts c l) a,LoadIndicies (Nexts c l) a)

stationaryCarrage :: forall (s::Nat) (c::Nat) (l::Nat) (e::Nat) a. Constr c l a => (forall s'. Carrage s' c l e a -> IO [[Double]]) -> IO ()
stationaryCarrage f = do
 c <- loadCarrage @s @c @l @e @a
 xs <- f c
 c' <- editCarrage xs c
 saveCarrage c'
 stationaryCarrage @s @c @l @e @a f

type family LessThan (x :: Nat) (y :: Nat) :: Bool where
    LessThan Z (S _) = 'True -- Zero is less than any successor
    LessThan (S x) (S y) = LessThan x y -- Compare the predecessors
    LessThan _ _ = 'False -- All other cases are false

class (Constr c l a,Recurse s c l e a) => MovingCarrage (s::Nat) (c::Nat) (l::Nat) (e::Nat) a where
 movingCarrage :: (forall c'.Carrage s c' l e a -> IO [[Double]]) -> IO ()

type family Recurse (s::Nat) (c::Nat) (l::Nat) (e::Nat) a ::Constraint where
 Recurse s c l e a = If (LessThan c e) (MovingCarrage s (S c) l e a) (()::Constraint) 

type family If (cond :: Bool) (true :: Constraint) (false :: Constraint) :: Constraint where
    If 'True true _ = true
    If 'False _ false = false



{-
{-
class (SaveIndicies (Nexts c l) a,SaveIndicies (Nexts (S s) l) a,Recurse s c l e a) => InfiniteConstraint (s::Nat) (c::Nat) (l::Nat) (e::Nat) a 
instance  (SaveIndicies (Nexts c l) a,SaveIndicies (Nexts (S s) l) a,Recurse s c l e a) => InfiniteConstraint s c l e a 
-}
{-
type InfiniteConstraint (s::Nat) (c::Nat) (l::Nat) (e::Nat) a = (UpdateIndicies (Nexts c l) a,SaveIndicies (Nexts c l) a,LoadIndicies (Nexts c l) a,Recurse s c l e a)
type family Recurse s c l e a ::Constraint where
 Recurse s c l (s) a = () 
 Recurse s c l e a = InfiniteConstraint s (S c) l e a
-}


{-
class    (Constr c l a) => InfiniteConstraint (s::Nat) (c::Nat) (l::Nat) (e::Nat) a 
instance (Constr c l a ,Choice s c l e a) => InfiniteConstraint (s::Nat) (c::Nat) (l::Nat) (e::Nat) a 
-}

--type InfiniteConstraint (s::Nat) (c::Nat) (l::Nat) (e::Nat) a = (Constr c l a ,Choice s c l e a) 
{-
class
    ( Constr c l a) =>  InfiniteConstraint (s :: Nat) (c :: Nat) (l :: Nat) (e :: Nat) a 
instance
    ( Constr c l a -- Constraints for the current index
    , If (e == (S c)) (() :: Constraint) (InfiniteConstraint s (S c) l e a) -- Recursive constraint
    ) =>  InfiniteConstraint (s :: Nat) (c :: Nat) (l :: Nat) (e :: Nat) a 
-}
{-
type family Choice (s::Nat) (c::Nat) (l::Nat) (e::Nat) a ::Constraint where
 Choice s c l c a = () 
 Choice s c l e a = InfiniteConstraint s (S c) l e a
-}

--

type Constr (c::Nat) (l::Nat) a = (SaveIndicies (Nexts c l) a,UpdateIndicies (Nexts c l) a,LoadIndicies (Nexts c l) a)

{-
type family InfiniteConstraint (s :: Nat) (c :: Nat) (l :: Nat) (e :: Nat) a :: Constraint where
 InfiniteConstraint s c l e a = If (e == (S c)) (() :: Constraint) (Constr c l a,InfiniteConstraint s (S c) l e a)
-}

type family InfiniteConstraint (s :: Nat) (c :: Nat) (l :: Nat) (e :: Nat) a :: Constraint where
    InfiniteConstraint s c l e a =
        ( Constr c l a -- Apply constraints for the current `c`
        , If (c == e)
             (() :: Constraint) -- Base case: Stop recursion when `c == e`
             ( If (LessThan c e) -- Recursive case: Only recurse if `c < e`
                  (InfiniteConstraint s (S c) l e a)
                  () -- (TypeError ('Text "Invalid constraint: c >= e in InfiniteConstraint"))
             )
        )

type family If (cond :: Bool) (true :: Constraint) (false :: Constraint) :: Constraint where
    If 'True true _ = true
    If 'False _ false = false

movingCarrage :: forall (s::Nat) (c::Nat) (l::Nat) (e::Nat) a. (InfiniteConstraint s c l e a) => (forall c'.Carrage s c' l e a -> IO [[Double]]) -> IO ()
movingCarrage f = do
 c <- loadCarrage @s @c @l @e @a
 xs <- f c
 c' <- editCarrage xs c
 saveCarrage c'
 recurse f

type family LessThan (x :: Nat) (y :: Nat) :: Bool where
    LessThan Z (S _) = 'True -- Zero is less than any successor
    LessThan (S x) (S y) = LessThan x y -- Compare the predecessors
    LessThan _ _ = 'False -- All other cases are false

{-
class Recurse (s :: Nat) (c :: Nat) (l :: Nat) (e :: Nat) a where
    recurse :: (forall c'. Carrage s c' l e a -> IO [[Double]]) -> IO ()

instance ((c == e) ~ 'True) => Recurse s c l e a where
    recurse _ = return () -- Base case: Stop recursion when `c == e`

instance ((c == e) ~ 'False, InfiniteConstraint s (S c) l e a) => Recurse s c l e a where
    recurse f = movingCarrage @s @(S c) @l @e @a f -- Recursive case: Continue with `S c`
-}

class Recurse (s :: Nat) (c :: Nat) (l :: Nat) (e :: Nat) a where
    recurse :: (forall c'. Carrage s c' l e a -> IO [[Double]]) -> IO ()

-- Base case: Stop recursion when `c == e`
instance ((c == e) ~ 'True) => Recurse s c l e a where
    recurse _ = return ()

-- Recursive case: Continue recursion when `c < e`
instance ((c == e) ~ 'False, LessThan c e ~ 'True, InfiniteConstraint s (S c) l e a) => Recurse s c l e a where
    recurse f = movingCarrage @s @(S c) @l @e @a f

-}