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
  _ <- insert "abc" "ABC" hm
  _ <- insert "def" "DEF" hm
  --
  assertEq (Just "ABC") !(lookup "abc" hm)
  assertEq (Just "DEF") !(lookup "def" hm)
  assertEq Nothing !(lookup "zzz" hm)
  putStrLn ""


main : IO ()
main = do
  putStrLn "Starting to test idris2-missing-containers"
  testHashMap
  putStrLn "Done"






