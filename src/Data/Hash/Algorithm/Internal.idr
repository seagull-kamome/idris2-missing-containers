module Data.Hash.Algorithm.Internal

import Data.Hash.Algorithm
import Data.Bits

%default total

-- ----------------------------------------------------------------------------

public export %inline rotL32, rotR32 : Bits32 -> Bits32 -> Bits32
rotL32 x n = (x `prim__shl_Bits32` n) .|. (x `prim__shr_Bits32` (32 - n))
rotR32 x n = (x `prim__shr_Bits32` n) .|. (x `prim__shl_Bits32` (32 - n))


public export %inline rotL64, rotR64 : Bits64 -> Bits64 -> Bits64
rotL64 x n = (x `prim__shl_Bits64` n) .|. (x `prim__shr_Bits64` (64 - n))
rotR64 x n = (x `prim__shr_Bits64` n) .|. (x `prim__shl_Bits64` (64 - n))


-- ----------------------------------------------------------------------------

export %inline feed8Of16 : HashAlgorithm algo _ _ => algo -> Bits16 -> algo
feed8Of16 h k = feed8 (feed8 h $ cast k) $ cast $ k `shiftR` 8

export %inline feed16Of32 : HashAlgorithm algo _ _ => algo -> Bits32 -> algo
feed16Of32 h k = feed8Of16 (feed8Of16 h $ cast k) $ cast $ k `shiftR` 16

export %inline feed32Of64 : HashAlgorithm algo _ _ => algo -> Bits64 -> algo
feed32Of64 h k = feed16Of32 (feed16Of32 h $ cast k) $ cast $ k `shiftR` 32

