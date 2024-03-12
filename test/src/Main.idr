module Main

import System.Info
import Data.String
import Data.IORef
import Decidable.Equality
import Data.Bits
import Data.Container.IOHashMap
import Data.Hash.Algorithm.FNV
import Data.Hash.Algorithm.MurMur3
import Data.Hash.Algorithm.OneAtATime
import Data.Hash.Algorithm.Sip

import System.File
import System.Clock

assertEq : HasIO io => Eq a => (expected:a) -> (actual:a) -> io ()
assertEq expected actual = do
  putStr $ if expected == actual then "✓" else "✗"


------------------------------------------------------------------------------

testHashMap : IO ()
testHashMap = do
  putStrLn "# testHashMap"
  putStr "> "
  --
  hm <- newIODHashMap {tv=(const String)} (hash MurMur3.empty)
  _ <- write hm "abc" "ABC"
  _ <- write hm "def" "DEF"
  --
  assertEq (Just "ABC") !(read hm "abc")
  assertEq (Just "DEF") !(read hm "def")
  assertEq Nothing !(read hm "zzz")
  putStrLn ""


------------------------------------------------------------------------------

readAllLines : File -> IO (Either FileError (List String))
readAllLines h = go [] where
  go : List String -> IO (Either FileError (List String))
  go xs = do
    Right str <- fGetLine h
      | Left err => pure $ Left err
    if str == ""
       then pure $ Right xs
       else go $ [str] ++ xs

-- NOTE: for_, traverse_ also foldlM cause crash with stack overflow.
go : List String -> (String -> IO ()) -> IO ()
go [] _ = pure ()
go (x::xs) f = f x >> go xs f

benchmarkHash : HashAlgorithm a _ _ => String -> a -> List String -> IO ()
benchmarkHash nm h words = do
    t0 <- clockTime Monotonic
    go words $ ignore . pure . hash h
    t1 <- clockTime Monotonic
    putStrLn $ "\{nm} : \{show $ timeDifference t1 t0}"
 
partial
benchmarkHashMap : IO ()
benchmarkHashMap = do
  putStrLn "# benchmarkHashMap"
  --
  dict <- do
    Right h <- openFile "test/input_large" Read
      -- | Left err => pure $ Left err
    Right xs <- readAllLines h
      -- | Left err => putStrLn $ show err
    closeFile h
    pure xs
  putStrLn "dict: \{show $ length dict}"
  --
  words <- do
    Right h <- openFile "test/words" Read
      -- -- | Left err => putStrLn $ show err
    Right xs <- readAllLines h
      -- | Left err => putStrLn $ show err
    closeFile h
    pure xs
  putStrLn "words: \{show $ length words}"

  --
  benchmarkHash "FNV1a" FNV.empty words
  benchmarkHash "MurMur3" MurMur3.empty words
  benchmarkHash "OneAtATime" OneAtATime.empty words
  benchmarkHash "Sip64" (newSipHash64 0 0) words
  benchmarkHash "Sip32" (newSipHash32 0 0) words
  --
  -- hm <- newIOHashMap (hash OneAtATime.empty)
  hm <- newIOHashMap (hash (newSipHash32 0 0))
  do
    c <- newIORef 0
    t0 <- clockTime Monotonic
    go dict $ \x => do
        n <- readIORef c
        writeIORef c (S n)
        ignore $ write hm x (show n)
    t1 <- clockTime Monotonic
    putStrLn "write: \{show $ timeDifference t1 t0}/\{show $ length dict}"
  --
  do
    t0 <- clockTime Monotonic
    go words $ ignore . read hm
    t1 <- clockTime Monotonic
    putStrLn "read: \{show $ timeDifference t1 t0}/\{show $ length words}"
  --
  pure ()




partial
main : IO ()
main = do
  putStrLn """
Starting to test idris2-missing-containers
codegen = \{System.Info.codegen}
"""
  testHashMap
  benchmarkHashMap
  putStrLn "Done"






