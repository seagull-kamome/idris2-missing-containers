module Main

import Decidable.Equality
import Data.Hashable
import Data.Container.IOHashMap

assertEq : HasIO io => Eq a => (expected:a) -> (actual:a) -> io ()
assertEq expected actual = do
  putStr $ if expected == actual then "✓" else "✗"



testHashMap : IO ()
testHashMap = do
  putStrLn "# testHashMap"
  putStr "> "
  --
  hm <- newIODHashMap {tv=(const String)}
  _ <- insert hm "abc" "ABC"
  _ <- insert hm "def" "DEF"
  --
  assertEq (Just "ABC") !(lookup hm "abc")
  assertEq (Just "DEF") !(lookup hm "def")
  assertEq Nothing !(lookup hm "zzz")
  putStrLn ""


main : IO ()
main = do
  putStrLn "Starting to test idris2-missing-containers"
  testHashMap
  putStrLn "Done"






