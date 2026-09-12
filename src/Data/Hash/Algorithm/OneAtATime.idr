-- Implementation of OneAtATime Hash Algorithm.
--  See reference implementaion
--      https://en.wikipedia.org/wiki/Jenkins_hash_function
--
-- Copyright 2024, Hattori, Hiroki
-- This file is released under the MIT license, see LICENSE for more detail.
--
module Data.Hash.Algorithm.OneAtATime

import public Data.Hash.Algorithm
import Data.Hash.Algorithm.Internal
import Data.Bits

%default total

-- ----------------------------------------------------------------------------

export data OneAtATime = MkOneAtATime Bits32

public export empty : OneAtATime
empty = MkOneAtATime 0

-- Single, non-interface-method byte-mixing step (see FNV.idr for why this
-- avoids boxed dictionary dispatch on the rc2 backend).
feed8' : Bits32 -> Bits8 -> Bits32
feed8' h k =
  let h' = h + (cast k)
      h'' = h' + (h' `shiftR` 10)
   in h'' `xor` (h'' `shiftL` 6)

%inline
covering public export
HashAlgorithm OneAtATime False Bits32 where
  finalize (MkOneAtATime h) =
    let h' = h `shiftL` 3
        h'' = h' `xor` (h' `shiftR` 11)
     in h'' + (h'' `shiftL` 15)
  --
  feed8 (MkOneAtATime h) k = MkOneAtATime $ feed8' h k
  -- Byte order matches Internal.idr's feed8Of16/feed16Of32/feed32Of64 chain:
  -- least-significant-byte first (`cast k` is fed before `k `shiftR` 8`, etc).
  feed16 (MkOneAtATime h) k =
    let h0 = feed8' h  (cast k)
        h1 = feed8' h0 (cast $ k `shiftR` 8)
     in MkOneAtATime h1
  feed32 (MkOneAtATime h) k =
    let h0 = feed8' h  (cast k)
        h1 = feed8' h0 (cast $ k `shiftR` 8)
        h2 = feed8' h1 (cast $ k `shiftR` 16)
        h3 = feed8' h2 (cast $ k `shiftR` 24)
     in MkOneAtATime h3
  feed64 (MkOneAtATime h) k =
    let h0 = feed8' h  (cast k)
        h1 = feed8' h0 (cast $ k `shiftR` 8)
        h2 = feed8' h1 (cast $ k `shiftR` 16)
        h3 = feed8' h2 (cast $ k `shiftR` 24)
        h4 = feed8' h3 (cast $ k `shiftR` 32)
        h5 = feed8' h4 (cast $ k `shiftR` 40)
        h6 = feed8' h5 (cast $ k `shiftR` 48)
        h7 = feed8' h6 (cast $ k `shiftR` 56)
     in MkOneAtATime h7

