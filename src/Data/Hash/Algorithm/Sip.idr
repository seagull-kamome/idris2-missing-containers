-- Implementation of SipHash1-3 and SipHash2-4 Algorithm.
--  See reference implementation 
--     https://github.com/veorq/SipHash
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
-- SipHash64 1-3

export data SipHash64 = MkSip64 Bits32 Bits64 Bits64 Bits64 Bits64

export newSipHash64 : Bits64 -> Bits64 -> SipHash64
newSipHash64 k0 k1 = MkSip64 0
                        (k0 `xor` 0x736f6d6570736575)
                        (k1 `xor` 0x646f72616e646f6d)
                        (k0 `xor` 0x6c7967656e657261)
                        (k1 `xor` 0x7465646279746573)

export
round64 : Bits64 -> Bits64 -> Bits64 -> Bits64
        -> (Bits64, Bits64, Bits64, Bits64)
round64 v0 v1 v2 v3 =
  let v0'1 = v0 + v1
      v1'1 = (v1 `rotL64` 13) `xor` v0'1
      v2'1 = v2 + v3
      v3'1 = (v3 `rotL64` 16) `xor` v2'1
      v0'3 = (v0'1 `rotL64` 32) + v3'1
      v3'2 = (v3'1 `rotL64` 21) `xor` v0'3
      v2'2 = v2'1 + v1'1
      v1'2 = (v1'1 `rotL64` 17) `xor` v2'2
      v2'3 = v2'2 `rotL64` 32
   in (v0'3, v1'2, v2'3, v3'2)


feedSip64 : SipHash64 -> Bits32 -> Bits64 -> SipHash64
feedSip64 (MkSip64 l v0 v1 v2 v3) n x =
  let m : Bits32 = (l `mod` 8) * 8
      v3' = v3 `xor` (prim__shl_Bits64 x $ cast {to=Bits64} m)
   in if (m + n * 8) < 64
     then MkSip64 (l + n) v0 v1 v2 v3'
     else let (v0', v1', v2', v3'0) = round64 v0 v1 v2  v3'
              v3'1 = v3'0 `xor` (prim__shr_Bits64 x $ cast $ 64 - m)
            in MkSip64 (l + n) v0'  v1' v2' v3'1


covering public export
HashAlgorithm SipHash64 False Bits64 where
  feed8 h x  = feedSip64 h 1 $ cast x
  feed16 h x = feedSip64 h 2 $ cast x
  feed32 h x = feedSip64 h 4 $ cast x
  feed64 h x = feedSip64 h 8 $ cast x
  feedString = feedCharOfString
  --
  finalize (MkSip64 l v0 v1 v2 v3) =
     let b : Bits64 = (cast l) `prim__shl_Bits64` 56
         (v0'1, v1'1, v2'1, v3'1) = round64 v0 v1 v2 (v3 `xor` b)
         (v0'2, v1'2, v2'2, v3'2) = round64 (v0'1 `xor` b) v1 (v2'1 `xor` 0xff) v3'1
         (v0'3, v1'3, v2'3, v3'3) = round64 v0'2 v1'2 v2'2 v3'2
         (v0'4, v1'4, v2'4, v3'4) = round64 v0'3 v1'3 v2'3 v3'3
         (v0'5, v1'5, v2'5, v3'5) = round64 v0'4 v1'4 v2'4 v3'4
     in ((v0'5 `xor` v1'5) `xor` v2'5) `xor` v3'5


-- ----------------------------------------------------------------------------
-- SipHash32 2-4

export data SipHash32 = MkSip32 Bits32 Bits32 Bits32 Bits32 Bits32

export newSipHash32 : Bits32 -> Bits32 -> SipHash32
newSipHash32 k0 k1 = MkSip32 0
                      (0 `xor` k0) (0 `xor` k1)
                      (0x6c796765 `xor` k0) (0x74656462 `xor` k1)

export
round32 : Bits32 -> Bits32 -> Bits32 -> Bits32 -> (Bits32, Bits32, Bits32, Bits32)
round32 v0 v1 v2 v3 =
  let v0'1 = v0 + v1
      v1'1 = (v1 `rotL32` 5) `xor` v0'1
      v2'1 = v2 + v3
      v3'1 = (v3 `rotR32` 8) `xor` v2'1
      v0'2 = (v0'1 `rotL32` 16) + v3'1
      v3'2 = (v3'1 `rotR32` 7) `xor` v0'2
      v2'2 = v2'1 + v1'1
      v1'2 = (v1'1 `rotR32` 13) `xor` v2'2
      v2'3 = v2'2 `rotR32` 16
   in (v0'2, v1'2, v2'3, v3'2)

feedSip32 : SipHash32 -> Bits32 -> Bits32 -> SipHash32
feedSip32 (MkSip32 l v0 v1 v2 v3) n x =
  let m : Bits32 = (l `mod` 8) * 8
      v3' = v3 `xor` (prim__shl_Bits32 x m)
   in if (m + n * 8) < 32
         then MkSip32 (l + n) v0 v1 v2 v3'
         else let (v0'1, v1'1, v2'1, v3'1) = round32 v0 v1 v2 v3'
                  (v0'2, v1'2, v2'2, v3'2) = round32 v0'1 v1'1 v2'1 v3'1
               in MkSip32 (l + n) v0'2 v1'2 v2'2
                          (v3'2 `xor` (prim__shr_Bits32 x $ 32 - m))

covering public export
HashAlgorithm SipHash32 False Bits32 where
  feed8 h x = feedSip32 h 1 $ cast x
  feed16 h x = feedSip32 h 2 $ cast x
  feed32 h x = feedSip32 h 4 $ cast x
  feed64 h x =
    let h32 = cast $ x `shiftR` 32
        l32 = cast x
     in feedSip32 (feedSip32 h 4 l32) 4 h32
  feedString = feedCharOfString
  --
  finalize (MkSip32 l v0 v1 v2 v3) =
    let b : Bits32 = l `prim__shr_Bits32` 24
        (v0'1, v1'1, v2'1, v3'1) = round32 v0 v1 v2 (v3 `xor` b)
        (v0'2, v1'2, v2'2, v3'2) = round32 v0'1 v1'1 v2'1 v3'1
        (v0'3, v1'3, v2'3, v3'3) = round32 (v0'2 `xor` b) v1'2 (v2'2 `xor` 0xff) v3'2
        (v0'4, v1'4, v2'4, v3'4) = round32 v0'3 v1'3 v2'3 v3'3
        (v0'5, v1'5, v2'5, v3'5) = round32 v0'4 v1'4 v2'4 v3'4
        (v0'6, v1'6, v2'6, v3'6) = round32 v0'5 v1'5 v2'5 v3'5
     in v1'6 `xor` v3'6



