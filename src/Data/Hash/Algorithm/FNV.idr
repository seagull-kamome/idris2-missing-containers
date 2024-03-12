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

covering public export
HashAlgorithm FNV1a False Bits64 where
  finalize (MkFNV1a h) = h
  --
  feed8 (MkFNV1a h) x =
    let h' = h * 0x000001000000001b3
     in MkFNV1a $ h' `xor` (cast {to=Bits64} x)
  feed16 = feed8Of16
  feed32 = feed16Of32
  feed64 = feed32Of64
  feedString = feedCharOfString



