-- Implementation of FNV Hash Algorithm.
--  See reference implementaion
--      https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function
--
-- Copyright 2024, Hattori, Hiroki
-- This file is released under the MIT license, see LICENSE for more detail.
--
module Data.Hash.Algorithm.FNV

import public Data.Hash.Algorithm
import Data.Hash.Algorithm.Internal
import Data.Bits

%default total

-- ----------------------------------------------------------------------------

export data FNV1a = MkFNV1a Bits64

public export empty  : FNV1a
empty = MkFNV1a 0xcbf29ce48422325

-- Single, non-interface-method byte-mixing step. Ordinary function calls
-- (unlike calls to `feed8` through the `HashAlgorithm` dictionary) are not
-- boxed dictionary dispatches on the rc2 backend, so chaining this plain
-- helper directly inside feed16/feed32/feed64 costs only the ONE dispatch
-- that invoking feed16/feed32/feed64 itself already costs.
feed8' : Bits64 -> Bits8 -> Bits64
feed8' h x =
  let h' = h * 0x000001000000001b3
   in h' `xor` (cast {to=Bits64} x)

%inline
covering public export
HashAlgorithm FNV1a False Bits64 where
  finalize (MkFNV1a h) = h
  --
  feed8 (MkFNV1a h) x = MkFNV1a $ feed8' h x
  -- Byte order matches Internal.idr's feed8Of16/feed16Of32/feed32Of64 chain:
  -- least-significant-byte first (`cast k` is fed before `k `shiftR` 8`, etc).
  feed16 (MkFNV1a h) k =
    let h0 = feed8' h  (cast k)
        h1 = feed8' h0 (cast $ k `shiftR` 8)
     in MkFNV1a h1
  feed32 (MkFNV1a h) k =
    let h0 = feed8' h  (cast k)
        h1 = feed8' h0 (cast $ k `shiftR` 8)
        h2 = feed8' h1 (cast $ k `shiftR` 16)
        h3 = feed8' h2 (cast $ k `shiftR` 24)
     in MkFNV1a h3
  feed64 (MkFNV1a h) k =
    let h0 = feed8' h  (cast k)
        h1 = feed8' h0 (cast $ k `shiftR` 8)
        h2 = feed8' h1 (cast $ k `shiftR` 16)
        h3 = feed8' h2 (cast $ k `shiftR` 24)
        h4 = feed8' h3 (cast $ k `shiftR` 32)
        h5 = feed8' h4 (cast $ k `shiftR` 40)
        h6 = feed8' h5 (cast $ k `shiftR` 48)
        h7 = feed8' h6 (cast $ k `shiftR` 56)
     in MkFNV1a h7



