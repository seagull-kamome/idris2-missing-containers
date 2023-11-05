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
  _ <- write hm "abc" "ABC"
  _ <- write hm "def" "DEF"
  --
  assertEq (Just "ABC") !(read hm "abc")
  assertEq (Just "DEF") !(read hm "def")
  assertEq Nothing !(read hm "zzz")
  putStrLn ""


main : IO ()
main = do
  putStrLn "Starting to test idris2-missing-containers"
  testHashMap
  putStrLn "Done"






