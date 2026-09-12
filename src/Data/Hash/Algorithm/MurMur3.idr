-- Implementation of MurMur3 Hash Algorithm.
--  See reference implementaion
--      https://en.wikipedia.org/wiki/MurmurHash
--
-- Copyright 2024, Hattori, Hiroki
-- This file is released under the MIT license, see LICENSE for more detail.
--
module Data.Hash.Algorithm.MurMur3

import public Data.Hash.Algorithm
import Data.Hash.Algorithm.Internal
import Data.Bits

%default total

-- ----------------------------------------------------------------------------

export data MurMur3 = MkMurMur3 Bits32 Bits32 Bits32

public export empty : MurMur3
empty = MkMurMur3 0x9747b28c 0 0

-- Single, non-interface-method byte-mixing step, taking h/l/c as separate
-- plain scalar arguments (h = running hash, l = byte counter, c = partial-
-- word carry) rather than a generic tuple -- matching Sip.idr's own
-- feedSip64/feedSip32 style, which threads named scalars rather than boxing
-- them into a tuple between steps (a tuple-based version of this helper was
-- tried first and measurably regressed performance, presumably from the
-- extra Pair allocations). Preserves the exact same per-byte state machine
-- (including the every-4th-byte flush/mix) as the original feed8 body, just
-- factored out of the constructor so it can be called repeatedly as a plain
-- function (not a boxed HashAlgorithm dictionary dispatch) from
-- feed16/feed32/feed64.
feed8' : Bits32 -> Bits32 -> Bits32 -> Bits8 -> MurMur3
feed8' h l c x =
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

%inline
covering export
HashAlgorithm MurMur3 False Bits32 where
  finalize (MkMurMur3 h l c) =
    let h1 = h `xor` l
        h2 = (h1 `xor` (h1 `shiftR` 16)) * 0x85ebca6b
        h3 = (h2 `shiftR` 13) * 0xc2b2ae35
     in h3 `xor` (h3 `shiftR` 16)
  feed8 (MkMurMur3 h l c) x = feed8' h l c x
  -- Byte order matches Internal.idr's feed8Of16/feed16Of32/feed32Of64 chain:
  -- least-significant-byte first (`cast k` is fed before `k `shiftR` 8`, etc).
  feed16 (MkMurMur3 h l c) k =
    let MkMurMur3 h0 l0 c0 = feed8' h l c (cast k)
     in feed8' h0 l0 c0 (cast $ k `shiftR` 8)
  feed32 (MkMurMur3 h l c) k =
    let MkMurMur3 h0 l0 c0 = feed8' h  l  c  (cast k)
        MkMurMur3 h1 l1 c1 = feed8' h0 l0 c0 (cast $ k `shiftR` 8)
        MkMurMur3 h2 l2 c2 = feed8' h1 l1 c1 (cast $ k `shiftR` 16)
     in feed8' h2 l2 c2 (cast $ k `shiftR` 24)
  feed64 (MkMurMur3 h l c) k =
    let MkMurMur3 h0 l0 c0 = feed8' h  l  c  (cast k)
        MkMurMur3 h1 l1 c1 = feed8' h0 l0 c0 (cast $ k `shiftR` 8)
        MkMurMur3 h2 l2 c2 = feed8' h1 l1 c1 (cast $ k `shiftR` 16)
        MkMurMur3 h3 l3 c3 = feed8' h2 l2 c2 (cast $ k `shiftR` 24)
        MkMurMur3 h4 l4 c4 = feed8' h3 l3 c3 (cast $ k `shiftR` 32)
        MkMurMur3 h5 l5 c5 = feed8' h4 l4 c4 (cast $ k `shiftR` 40)
        MkMurMur3 h6 l6 c6 = feed8' h5 l5 c5 (cast $ k `shiftR` 48)
     in feed8' h6 l6 c6 (cast $ k `shiftR` 56)


