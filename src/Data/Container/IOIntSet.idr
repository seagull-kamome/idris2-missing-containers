-- Implimentation of mutable set of Int.
-- 
-- Copyright 2023, HATTORI, Hiroki
-- This file is released under the MIT license, see LICENSE for more detail.  
--
module Data.Container.IOIntSet

import Data.Bits
import Data.Maybe
import Data.Container.IOIntMap

%default total

-- --------------------------------------------------------------------------

export
record IOIntSet where
  constructor MkIOIntSet
  table: IOIntMap Bits64

public export newIOIntSet : HasIO io => io IOIntSet
newIOIntSet = pure $ MkIOIntSet !(newIOIntMap {t=Bits64})


public export read: HasIO io => IOIntSet -> (i:Int) -> io Bool
read im i = do
  Just j <- read im.table (i `div` 64) | Nothing => pure False
  pure $ (prim__and_Bits64 j (1 `prim__shl_Bits64` (cast $ i `mod` 64))) /= 0


public export write : HasIO io => IOIntSet -> (i:Int) -> io Bool
write im i = update im.table (i `div` 64) $ (pure . go)
  where
    msk: Bits64
    msk = prim__shl_Bits64 1 $ cast $ i `mod` 64
    go: Maybe Bits64 -> (Bool, Maybe Bits64)
    go Nothing  = (False, Just msk)
    go (Just j) = ((j `prim__and_Bits64` msk) /= 0, Just (j `prim__or_Bits64` msk))


public export delete : HasIO io => IOIntSet -> (i:Int) -> io Bool
delete im i = update im.table (i `div` 64) $ (pure . go)
  where
    msk: Bits64
    msk = prim__shl_Bits64 1 $ cast $ i `mod` 64
    go: Maybe Bits64 -> (Bool, Maybe Bits64)
    go Nothing  = (False, Nothing)
    go (Just j) =
      let k = prim__and_Bits64 j  (prim__negate_Bits64 msk) in
      if k == 0
        then (True, Nothing)
        else (True, Just k)

public export %inline clear: HasIO io => IOIntSet -> io ()
clear is = clear is.table

public export %inline count: HasIO io => IOIntSet -> io Int
count is = count is.table

public export %inline toList: HasIO io => IOIntSet -> io (List Int)
toList is = fold is.table (\acc, x => pure $ acc ++ (map cast $ h $ snd x)) []
 where
   h: Bits64 -> List Bits64
   h x = filter (\i => prim__and_Bits64 x (prim__shl_Bits64 1 i) /= 0) $ the (List Bits64) [0..64]

public export %inline union: HasIO io => IOIntSet -> IOIntSet -> io ()
union lhs rhs = fold rhs.table (\_, (i ** bits) =>
  update lhs.table i $ \case
    Just bits' => pure $ ((), Just $ prim__or_Bits64 bits bits')
    Nothing => pure ((), Just bits)) ()

public export %inline intersect: HasIO io => IOIntSet -> IOIntSet -> io ()
intersect lhs rhs = fold rhs.table (\_, (i ** bits) =>
  update lhs.table i $ \case
    Just bits' => pure $ ((), Just $ prim__and_Bits64 bits bits')
    Nothing => pure ((), Nothing)) ()

public export %inline except: HasIO io => IOIntSet -> IOIntSet -> io ()
except lhs rhs = fold rhs.table (\_, (i ** bits) =>
  update lhs.table i $ \case
    Just bits' => pure $ ((), Just $ prim__and_Bits64 bits $ prim__negate_Bits64 bits')
    Nothing => pure ((), Nothing)) ()

public export %inline fold: HasIO io => IOIntSet -> (g:acc -> Int -> io acc) -> acc -> io acc
fold is g acc = fold is.table (\acc', (i ** bits) => foldlM g acc' [i..(i+63)]) acc


