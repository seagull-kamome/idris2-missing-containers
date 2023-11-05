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




