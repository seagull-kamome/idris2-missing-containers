-- Implementation of SipHash1-3 Algorithm.
--  See reference implementation 
--     https://github.com/veorq/SipHash/blob/master/siphash.c
--
-- Copyright 2024, Hattori, Hiroki
-- This file is released under the MIT license, see LICENSE for more detail.
--

module Data.Hash.Algorithm.Sip

import public Data.Hash.Algorithm
import Data.Hash.Algorithm.Internal
import Data.Bits

%default total

-- ----------------------------------------------------------------------------

export data SipHash = MkSip Bits32 Bits64 Bits64 Bits64 Bits64 Bits64

public export newSipHash : Bits64 -> Bits64 -> SipHash
newSipHash k0 k1 = MkSip 0 0
                        (k0 `xor` 0x736f6d6570736575)
                        (k1 `xor` 0x646f72616e646f6d)
                        (k0 `xor` 0x6c7967656e657261)
                        (k1 `xor` 0x7465646279746573)


compress : Bits64 -> Bits64 -> Bits64 -> Bits64
        -> (Bits64, Bits64, Bits64, Bits64)
compress v0 v1 v2 v3 =
  let v0'1 = v0 + v1
      v1'1 = (v1 `rotL` 13) `xor` v0'1
      v2'1 = v2 + v3
      v3'1 = (v3 `rotL` 16) `xor` v2'1
      v0'3 = (v0'1 `rotL` 32) + v3'1
      v3'2 = (v3'1 `rotL` 21) `xor` v0'3
      v2'2 = v2'1 + v1'1
      v1'2 = (v1'1 `rotL` 17) `xor` v2'2
      v2'3 = v2'2 `rotL` 32
   in (v0'3, v1'2, v2'3, v3'2)


sipRound : SipHash -> Bits32 -> Bits64 -> SipHash
sipRound (MkSip l b v0 v1 v2 v3) n x =
  let m : Bits32 = (l `mod` 8) * 8
      b' : Bits64 = b .|. (prim__shl_Bits64 x $ cast {to=Bits64} m)
   in if (m + n * 8) < 64
     then MkSip (l + n) b' v0 v1 v2 v3
     else let v3_0 = v3 `xor` b'
              (v0', v1', v2', v3') = compress v0 v1 v2  v3
            in MkSip (l + n) (prim__shr_Bits64 x $ cast $ 64 - m) (v0 `xor` b') v1 v2 v3


covering public export
HashAlgorithm SipHash False Bits64 where
  feed8 h x = sipRound h 1 $ cast x
  feed16 h x = sipRound h 2 $ cast x
  feed32 h x = sipRound h 4 $ cast x
  feed64 h x = sipRound h 8 $ cast x
  feedString = feedCharOfString
  --
  finalize (MkSip l b v0 v1 v2 v3) =
     let b' : Bits64 = (cast $ l `mod` 0xff) `prim__shr_Bits64` 56
         (v0'1, v1'1, v2'1, v3'1) = compress v0 v1 v2 (v3 `xor` b')
         (v0'2, v1'2, v2'2, v3'2) = compress (v0'1 `xor` b') v1 (v2'1 `xor` 0xff) v3'1
         (v0'3, v1'3, v2'3, v3'3) = compress v0'2 v1'2 v2'2 v3'2
         (v0'4, v1'4, v2'4, v3'4) = compress v0'3 v1'3 v2'3 v3'3
         (v0'5, v1'5, v2'5, v3'5) = compress v0'4 v1'4 v2'4 v3'4
     in ((v0'5 `xor` v1'5) `xor` v2'5) `xor` v3'5




