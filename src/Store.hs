{-#Language BangPatterns,TypeApplications,ScopedTypeVariables,RankNTypes,AllowAmbiguousTypes#-}
module Store where
import Data.Maybe (maybe)
import System.Directory
{-
a store is an instance of class that has Read and Show as superclasses
these instances implement String name, and a 0th instance
this is used in a cascade function, which suffixes an itteration number.

stores are not reproduced if existing, and so are accessed within the IO monad,
given that in the case they exist, they are loaded (readFile + read)
such that in the cascade opperation, there can be no overwrites, hence the version number.

the cascade takes a morphism to take the previous version to the next.

in the case where an object is parametricly supported in its actual parameters, and only the 
supporting coeffecients are to be stored (along with any shape data) this is reflected in the Read and Show instances.
to avoid the complexity of having to instantiate the Read class, which uses algebraic parsing streaming,
an alternative Save,Load interface is given.
-}

(+/+) :: String -> String -> String
(+/+) a b = a ++"//"++ b
  
---
-- Save & Load

class Save a where
 encode :: a -> String
 
save :: Save a => FilePath -> a -> IO ()
save path a = do
 writeFile path $ encode a
 
class Load a where
 decode :: String -> a

load :: Load a => FilePath -> IO a
load path = decode <$> readFile path 

---
-- Store

class (Save a,Load a) => Store a where
 storeName :: String
 storeInitialization :: a

storePath :: forall a. Store a => Int -> FilePath
storePath i = name +/+ (name ++ "." ++ (show i) ++ ".store")
 where
  name = storeName @a
 
doesStoreExist :: forall a. Store a => Int -> IO Bool
doesStoreExist i = doesFileExist path
 where
  path = storePath @a i
 
writeStore :: forall a. Store a => Int -> a -> IO ()
writeStore i a = do
 createDirectoryIfMissing True name
 b <- doesStoreExist @a i
 if b then error "store functionality precludes overwrites." else save path a
 where
  path = storePath @a i
  name = storeName @a
  
writeNextStore :: forall a. Store a => a -> IO ()
writeNextStore a = do
 n <- nextStoreNumber @a
 writeStore n a

readStore :: forall a. Store a => Int -> IO (Maybe a)
readStore i = do
 createDirectoryIfMissing True name
 b <- doesStoreExist @a i
 if not b then return Nothing else Just <$> load path
 where
  path = storePath @a i
  name = storeName @a
  
readStoreUnsafe :: forall a. Store a => Int -> IO a
readStoreUnsafe i = fromJust <$> readStore i
   where
    fromJust Nothing = error "fromJust used in readStoreUnsafe."
    fromJust (Just a) = a

 
---

cleanStore :: forall a. Store a => IO ()
cleanStore = removePathForcibly name
 where
  name = storeName @a

cleanEmptyStores :: forall a. Store a => IO ()
cleanEmptyStores = do
 xs <- filter (flip elem [".",".."]) <$> (getDirectoryContents $ storeName @a)
 ys <- traverse getFileSize xs
 let zs = zip xs ys
 let ws = fst $ unzip $ filter ((0==) . snd) zs
 traverse removePathForcibly ws
 return ()
-- used when reading

lastStoreNumber :: forall a. Store a => IO Int
lastStoreNumber = do
 b <- doesDirectoryExist name
 if not b then return 0 else do
  xs <- getDirectoryContents name
  return $ (length xs) - 2 -- -2 as removes '.','..' paths
   where
    name = storeName @a

lastStorePath :: forall a. Store a => IO FilePath
lastStorePath = storePath @a <$> lastStoreNumber @a   

-- no store may not exist, so it will return the initialisation
lastStore :: forall a. Store a => IO a
lastStore = do
 createDirectoryIfMissing True $ storeName @a
 cleanEmptyStores @a
 n <- lastStoreNumber @a
 if 0 == n then return (storeInitialization @a) else fromJust <$> readStore n
   where
    fromJust Nothing = error "fromJust used in lastStore on missing store path."
    fromJust (Just a) = a

-- used when writing
nextStoreNumber :: forall a. Store a => IO Int
nextStoreNumber = (+1) <$> lastStoreNumber @a 

nextStorePath :: forall a. Store a => IO FilePath
nextStorePath = storePath @a <$> nextStoreNumber @a   
 {-
-- a process that will not perform an opperation to create an object if it is already stored
store :: forall a. Store a => Int -> (a,a->IO a) -> IO a
store i (b,f) = readStore @a i >>= maybe (f b) f
  -}
nextStore :: forall a. Store a => (a->IO a) -> IO a
nextStore f = do
 a <- lastStore @a
 n1 <- lastStoreNumber @a
 n2 <- nextStoreNumber @a
 b <- f a -- store n1 (a,f) 
 writeStore n2 b
 return b
  
-- a process that given the store initialization, will produce an infinite sequence of stored objects using a given opperation.
cascade :: forall a. Store a => Bool -> (a->IO a) -> IO ()
cascade overwrite f = do
 if overwrite then cleanStore @a >> cascade False f else do
  a <- lastStore @a
  b <- nextStore f
 -- print $ encode b
  cascade False f

streamed :: forall a x. Store a => Bool -> x -> (x->Bool,x->x,x -> IO a) -> IO ()
streamed overwrite x (h,f,g) = do
 if not $ h x then return () else do
  if overwrite then cleanStore @a >> streamed False x (h,f,g) else do
   a <- lastStore @a
   b <- nextStore (const (g x))
 --  print $ encode b
   streamed False (f x) (h,f,g)
  
streamedList :: forall a x. Store a => Bool -> [x] -> (x -> IO a) -> IO ()
streamedList overwrite x f = do
 n <- lastStoreNumber @a
 streamed overwrite (drop n x) (not.null,tail,f.head) 

data TestStore = TestStore Int deriving (Read,Show)

incramentTestStore :: TestStore -> IO TestStore
incramentTestStore (TestStore n) = return $ TestStore (n+1)

doubleTestStore :: TestStore -> IO TestStore
doubleTestStore (TestStore n) = return $ TestStore (n*2)

instance Save TestStore where
 encode = show
 
instance Load TestStore where
 decode = read
 
instance Store TestStore where
 storeName = "testStore"
 storeInitialization = TestStore 0
 
testStore1 :: IO ()
testStore1 = cascade True incramentTestStore 

testStore2 :: IO ()
testStore2 = cascade False incramentTestStore  

cleanTests :: IO ()
cleanTests = cleanStore @TestStore

eg :: IO TestStore
eg = lastStore @TestStore

testStream :: IO ()
testStream = streamedList True [TestStore x|x<-[1..10]] doubleTestStore

---

wholeStore :: forall a. Store a => IO [a]
wholeStore = do
 n <- lastStoreNumber @a
 let xs = [1..n]
 traverse (readStoreUnsafe @a) xs

storeMap :: forall a b. (Store a,Store b) => (a -> IO b) -> IO ()
storeMap f = do
 n <- lastStoreNumber @a
 let xs = [1..n]
-- streamedList :: forall a x. Store a => Bool -> [x] -> (x -> IO a) -> IO ()
 streamedList False xs (\n -> readStoreUnsafe @a n >>= f)

storeTraverse :: forall a b c. Store a => (a -> b) -> ([b] -> IO c) -> IO c
storeTraverse f g = wholeStore >>= g . map f

