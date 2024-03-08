module Data.Hash.Algorithm.MurMur3

import public Data.Hash.Algorithm
import Data.Hash.Algorithm.Internal
import Data.Bits

%default total

-- ----------------------------------------------------------------------------

export data MurMur3 = MkMurMur3 Bits32 Bits32 Bits32

public export empty : MurMur3
empty = MkMurMur3 0x9747b28c 0 0

covering export
HashAlgorithm MurMur3 False Bits32 where
  finalize (MkMurMur3 h l c) =
    let h1 = h `xor` l
        h2 = (h1 `xor` (h1 `shiftR` 16)) * 0x85ebca6b
        h3 = (h2 `shiftR` 13) * 0xc2b2ae35
     in h3 `xor` (h3 `shiftR` 16)
  feed8 (MkMurMur3 h l c) x =
    let l' = l + 1
        c' = c `shiftL` 8
     in if l' `mod` 4 == 0
       then
         let x1 = c' * 0xcc9e2d51
             h1 = h `xor` (((x1 `shiftL` 15) .|. (x1 `shiftR` 17)) * 0x1b873593)
             h2 = ((h1 `shiftL` 13) .|. (h1 `shiftR`  19)) * 5 + 0xe6546b64
          in MkMurMur3 h2 l' 0
        else
          MkMurMur3 h l' ((c `shiftL` 8) .|. (cast x))
  feed16 = feed8Of16
  feed32 = feed16Of32
  feed64 = feed32Of64
  feedString = feedCharOfString



