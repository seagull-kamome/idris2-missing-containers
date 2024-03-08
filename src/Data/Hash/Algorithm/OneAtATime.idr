module Data.Hash.Algorithm.OneAtATime

import public Data.Hash.Algorithm
import Data.Hash.Algorithm.Internal
import Data.Bits

%default total

-- ----------------------------------------------------------------------------

export data OneAtATime = MkOneAtATime Bits32

public export empty : OneAtATime
empty = MkOneAtATime 0


covering public export
HashAlgorithm OneAtATime False Bits32 where
  finalize (MkOneAtATime h) = 
    let h' = h `shiftL` 3
        h'' = h' `xor` (h' `shiftR` 11)
     in h'' + (h'' `shiftL` 15)
  --
  feed8 (MkOneAtATime h) k =
    let h' = h + (cast k)
        h'' = h' + (h' `shiftR` 10)
     in MkOneAtATime $ h'' `xor` (h'' `shiftL` 6)
  feed16 = feed8Of16
  feed32 = feed16Of32
  feed64 = feed32Of64
  feedString k h = feedCharOfString k h


