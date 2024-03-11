module Data.Hash.Algorithm.Internal

import Data.Hash.Algorithm
import Data.Bits

%default total

-- ----------------------------------------------------------------------------

export feed8Of16 : HashAlgorithm algo _ _ => algo -> Bits16 -> algo
feed8Of16 h k = feed8 (feed8 h $ cast k) $ cast $ k `shiftR` 8

export feed16Of32 : HashAlgorithm algo _ _ => algo -> Bits32 -> algo
feed16Of32 h k = feed16 (feed16 h $ cast k) $ cast $ k `shiftR` 16

export feed32Of64 : HashAlgorithm algo _ _ => algo -> Bits64 -> algo
feed32Of64 h k = feed32 (feed32 h $ cast k) $ cast $ k `shiftR` 32


export feedCharOfString : HashAlgorithm algo _ _  => algo -> String -> algo
feedCharOfString h k = go (prim__strLength k) 0 h where
  go : Int -> Int -> algo -> algo
  go len n h = if len <= n
                  then h
                  else go len (assert_smaller n $ n + 1)
                          $ feed8 h (cast {to=Bits8} (assert_total $ prim__strIndex k n))

