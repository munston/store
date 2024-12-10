{-# Language TypeFamilies , FlexibleContexts , UndecidableInstances , GADTs , FlexibleInstances , MultiParamTypeClasses , TypeOperators , ConstraintKinds , ScopedTypeVariables , TypeApplications , KindSignatures , DataKinds , AllowAmbiguousTypes#-}
module Indexed where
--conumer of the Store and Counter (Indexed), that sequentially produces IO () effects

import Store
import Nat
import Data.Proxy
---
-- Counter

fromProxyNat :: forall n. FromNat n => Proxy (n::Nat) -> Int
fromProxyNat _ = fromNat @n

class CounterT a (n::Nat) where
 type Next a n :: Nat
 nextT :: a n -> a (Next a n)

type family Advance a (n::Nat) (m::Nat) :: Nat where
 Advance a n Z = n
 Advance a n (S m) = Next a (Advance a n m)
 
type family Nexts a (n :: Nat) (m :: Nat) :: [Nat] where
 Nexts a n Z = '[]
 Nexts a n (S m) = n ': Nexts a (Next a n) m

data Nats (ns :: [Nat]) = Nats

consNats :: forall n ns. Proxy (n::Nat) -> Nats ns -> Nats (n ': ns)
consNats _ _ = Nats

counterT :: CounterT a n => a n -> Proxy n
counterT _ = Proxy

indexT :: CounterT a n => a n -> Proxy n
indexT _ = Proxy

class Counter a where
 next :: a -> a
 counter :: a -> Int

count :: Counter a => a -> (a,Int)
count a = (next a,counter a)

countT :: (CounterT a n,FromNat n) => a n -> (a (Next a n),Int)
countT a = (nextT a,fromProxyNat $ counterT a)

data UnboundedCounter = UnboundedCounter Int

data UnboundedCounterT (n::Nat) = UnboundedCounterT Int

instance Counter UnboundedCounter where
 next (UnboundedCounter n) = UnboundedCounter (n+1)
 counter (UnboundedCounter n) = n

testUnbounded = let a = UnboundedCounter 0 in loop a
 where
  loop a = print (counter a) >> loop (next a)

instance CounterT UnboundedCounterT n where
 type Next UnboundedCounterT n = S n
 nextT (UnboundedCounterT n) = UnboundedCounterT (n+1)

testUnboundedT = loop a
 where
  a :: UnboundedCounterT 'Z
  a = UnboundedCounterT 0 
  loop :: forall n a. FromNat a => UnboundedCounterT a -> IO ()
  loop a = let (a',n) = countT a in print n >> loop a'

-- used to populate a list
class Counter a => BoundedCounter a where
 bound :: a -> Int

boundedCounter :: BoundedCounter a => a -> (a,[Int])
boundedCounter a = loop (bound a) a
 where
  loop 0 a = (a,[])
  loop n a = let (a',xs) = loop (n-1) (next a) in (a',x:xs) where x = counter a

class CounterT a n => BoundedCounterT a n where
 type Bound a n :: Nat
 boundT :: a n -> Int

boundedCounterT :: forall (a :: Nat -> *) (n :: Nat). BoundedCounterT a n => a n -> (a (Plus (Bound a n) n),Nats (Nexts a n (Bound a n)))
boundedCounterT a = boundedLoop @a @(Bound a n) (Proxy @(Bound a n)) (boundT a) a

class BoundedLoop (m::Nat) (a :: Nat -> *) (n :: Nat) where
 boundedLoop :: Proxy m -> Int -> a n -> (a (Advance a n m),Nats (Nexts a n (Bound a n)))

instance BoundedLoop m a Z where
  boundedLoop _ 0 a = (a,EmptyIndicies)


instance BoundedLoop m a n => BoundedLoop (S m) a (S n) where--
  boundedLoop _ np1 a = let (a',nats) = boundedLoop @a @n (Proxy @n) (np1-1) (nextT a) 
                            x = indexT a
                        in (a',consNats @(S n) @(Nexts a n (Bound a n)) x nats) 

-- the modulo group Zn (unmodifiable). (position,extent)
data Zn = Zn Int Int

data ZN (n::Nat) = ZN Int Int

instance Counter Zn where
 next (Zn i n) = Zn (mod (i+1) n) n
 counter (Zn i _) = i

instance CounterT ZN n where
 type Next ZN n = Mod (S n) (Bound ZN n)
 nextT (ZN i n) = ZN (mod (i+1) n) n

instance BoundedCounter Zn where
 bound (Zn i n) = n

testZn :: IO ()
testZn = do
 let (a,xs) = boundedCounter (Zn 0 10)
 traverse print xs
 putStrLn ""
 let (_,ys) = boundedCounter a
 traverse print ys
 return ()

-- a carrage of length n. (current position,length of carrage,start index)
-- used as a source until end of carrage length, then restarts at startIndex+1
data Carrage = Carrage Int Int Int

instance Counter Carrage where
 next (Carrage i l start) = Carrage i'' l start'
  where
   i' = (i+1)
   (i'',start') = if i' >= (start+l) then (start+1,start+1) else (i',start)
 counter (Carrage i l start) = i

-- this will initialise a buffer, when used again, will shift the buffer along (insane autobuffering wth!)
instance BoundedCounter Carrage where
 bound (Carrage i l start) = l

testCarrage :: IO ()
testCarrage = do
 let (a,xs) = boundedCounter (Carrage 0 10 0)
 traverse print xs
 putStrLn ""
 let (_,ys) = boundedCounter a
 traverse print ys
 return ()


---
-- combining Counter and Store. Indexed

-- the Nat and Int are the *same* !! by smart constructor.
data Indexed (n::Nat) a = Indexed Int a

data Indicies (ns::[Nat]) a where
 EmptyIndicies :: Indicies '[] a
 ConsIndicies :: (FromNat n,Store a) => Indexed n a -> (Indicies ns a) -> Indicies (n ': ns) a

class UpdateIndicies ns a where
 updateIndicies :: (a -> IO a) -> Indicies ns a -> IO (Indicies ns a)

instance UpdateIndicies '[] a where
 updateIndicies f EmptyIndicies = return EmptyIndicies

instance UpdateIndicies ns a => UpdateIndicies (n ': ns) a where
 updateIndicies f (ConsIndicies (Indexed n a) xs) = do
  a' <- f a
  xs' <- updateIndicies f xs
  return $ ConsIndicies (Indexed n a') xs'

class SaveIndicies ns a where
 saveIndicies :: Indicies ns a -> IO ()

instance SaveIndicies '[] a where
 saveIndicies EmptyIndicies  = return ()

instance SaveIndicies ns a => SaveIndicies (n ': ns) a where
 saveIndicies (ConsIndicies a xs) = writeNextStore a >> saveIndicies xs

-- make sure this matches up with however the populate and Counter interact.
--class BufferIndicies ns a where

instance Functor (Indexed n) where
 fmap f (Indexed i a) = Indexed i (f a)

instance Load a => Load (Indexed n a) where
 decode xs = let n = read @Int (takeWhile (/= ':') xs) in (Indexed n $ decode (tail (dropWhile (/=':') xs)))

instance Save a => Save (Indexed n a) where
 encode (Indexed n a) = (show n) ++ ":" ++ encode a

-- central constraint
type Index n a = (FromNat n,Store a) 

instance Index n a => Store (Indexed n a) where
 storeName = storeName @a ++ "." ++ (show $ fromNat @n)
 storeInitialization = Indexed (fromNat @n) (storeInitialization @a)

data EgStore = EgStore String deriving Show

flipEgStore :: EgStore -> EgStore
flipEgStore (EgStore xs) = EgStore $ reverse xs

flipper :: EgStore -> IO EgStore
flipper x = print y >> return y
 where
  y = flipEgStore x

instance Load EgStore where
 decode = EgStore

instance Save EgStore where
 encode (EgStore a) = a

instance Store EgStore where
 storeName = "eg store"
 storeInitialization = EgStore "hello eg store"

test = do
 t1
 t2
 t1
 t2
 where
  t1 = lastStore @(Indexed 'Z EgStore) >>= putStrLn . encode
  t2 = nextStore @(Indexed 'Z EgStore) (return . fmap flipEgStore)

class (Store a,UpdateIndicies ns a,SaveIndicies ns a) => Populate ns a where
 populate :: Counter b => b -> (b,IO (Indicies ns a))

instance (Store a,UpdateIndicies '[] a,SaveIndicies '[] a) => Populate '[] a where
 populate a = (a,return EmptyIndicies)

instance (FromNat n,Populate ns a,Store a,UpdateIndicies (n ': ns) a,SaveIndicies (n ': ns) a) => Populate (n ': ns) a where
 populate a = if not check then error "populate" else (a'',b >>= \x -> ps >>= \y -> return $ ConsIndicies x y)
  where
   (a',n) = count a
   (a'',ps) = populate @ns a' 
   b = lastStore @(Indexed n a)
   check = fromNat @n == n

testIndicies :: forall (ns::[Nat]) a.Populate ns a => (a -> IO a) -> IO ()
testIndicies f = do
 let (a,b) = populate @ns @a $ UnboundedCounter 0
 x <- b
 y <- updateIndicies f x
 saveIndicies y
 return ()

runTestIndicies :: IO ()
runTestIndicies = testIndicies @'[Z,S Z,S (S Z)] @EgStore flipper

go = runTestIndicies 

-- its kind of a fuck up to use counter with the type level nats of the indicies
-- they have to match up! can just use them anyway. 

{-
class Load a where
 decode :: String -> a
class Save a where
 encode :: a -> String
class (Save a,Load a) => Store a where
 storeName :: String
 storeInitialization :: a
-}

