-- Interface definitions of HashAlgorithm.
--
-- Copyright 2024, HATTORI, Hiroki
-- This file is released under the MIT license, see LICENSE for more detail.
--
module Data.Hash.Algorithm

import Data.Bits

%default total

-- ----------------------------------------------------------------------------

export
interface HashAlgorithm (0 algo:Type) (0 crypt:Bool) (0 ty:Type) | algo where
  export finalize : algo -> ty
  --
  feed8 : algo -> Bits8 -> algo
  feed16 : algo -> Bits16 -> algo
  feed32 : algo -> Bits32 -> algo
  feed64 : algo -> Bits64 -> algo
  feedString : algo -> String -> algo

-- ----------------------------------------------------------------------------

public export
interface Hashable (0 a:Type) where
  feed : HashAlgorithm algo crypt ty => algo -> a -> algo

infixl 8 `feed`

public export
Hashable Bool where
  feed h True = feed8 h 1
  feed h False = feed8 h 0
public export Hashable Char where feed h x = feed8 h (cast x)
public export Hashable Bits8 where feed = feed8
public export Hashable Bits16 where feed = feed16
public export Hashable Bits32 where feed = feed32
public export Hashable Bits64 where feed = feed64
public export Hashable Int8 where feed h x = feed8 h (cast x)
public export Hashable Int16 where feed h x = feed16 h (cast x)
public export Hashable Int32 where feed h x = feed32 h (cast x)
public export Hashable Int64 where feed h x = feed64 h (cast x)
public export Hashable String where feed = feedString

-- Hashable Double where hashWithSalt = feedString
public export
Hashable Integer where
  feed h x = go x $ if x >= 0 then h else feed8 h 1 where
    cail : Integer
    cail = (1 `shiftL` 64) - 1
    go : Integer -> algo -> algo
    go x h  =
      if x > cail
         then go (assert_smaller x $ x `shiftR` 64)
                 (feed64 h $ cast {to=Bits64} $ x .&. cail)
         else feed64 h $ cast {to=Bits64} x

public export hash : HashAlgorithm algo _ ty => Hashable a => algo -> a -> ty
hash h a = finalize $ feed h a


public export
Hashable Nat where feed h x = feed h $ cast {to=Integer} x

public export
Traversable f => Hashable a => Hashable (f a) where
  feed h xs = foldl feed h xs


