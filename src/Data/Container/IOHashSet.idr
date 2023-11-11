-- Implimentation of mutable dependent and independent type hash map.
-- 
-- Copyright 2023, HATTORI, Hiroki
-- This file is released under the MIT license, see LICENSE for more detail.  
--
module Data.Container.IOHashSet

import Data.Maybe
import Decidable.Equality
import Data.Hashable

import Data.Container.Internal.IOHashSet

%default total

-- --------------------------------------------------------------------------

export
record IOHashSet t where
  constructor MkIOHashSet
  table: IOHashSet' t t

DecEq t => IsHashSet' (IOHashSet' t t) t t where
  keyfunc _ = id

public export %inline newIOHashSet : HasIO io => Hashable t => DecEq t =>
 io (IOHashSet t)
newIOHashSet = pure $ MkIOHashSet !(newIOHashSet' (cast . hash))


public export %inline read: HasIO io => DecEq t => IOHashSet t -> t -> io Bool
read hs k = runIOHashSet hs.table k (pure . Left . isJust)

public export %inline write: HasIO io => DecEq t => IOHashSet t -> t -> io Bool
write hs k = runIOHashSet hs.table k (\x => pure $ Right (isJust x, Just k))

public export %inline delete: HasIO io => DecEq t => IOHashSet t -> t -> io Bool
delete hs k = runIOHashSet hs.table k (\x => pure $ Right (isJust x, Nothing))

public export %inline clear: HasIO io => IOHashSet t -> io ()
clear hs = clear hs.table

public export %inline count: HasIO io => IOHashSet t -> io Int
count hs = count hs.table

public export %inline toList: HasIO io => IOHashSet t -> io (List t)
toList hs = toList hs.table

public export %inline union: HasIO io => DecEq t =>
  IOHashSet t -> IOHashSet t -> io ()
union lhs rhs = foldIOHashSet rhs.table (\_, x =>
  write lhs x >>= \_ => pure (True, ())) ()

public export %inline intersect: HasIO io => DecEq t =>
  IOHashSet t -> IOHashSet t -> io ()
intersect lhs rhs = filterIOHashSet lhs.table (read rhs)

public export %inline except: HasIO io => DecEq t =>
  IOHashSet t -> IOHashSet t -> io ()
except lhs rhs = filterIOHashSet lhs.table (read rhs >=> pure . not)

public export %inline fold: HasIO io => DecEq t => 
  IOHashSet t -> (acc -> t -> io acc) -> acc -> io acc
fold hm f = foldIOHashSet hm.table $ \acc', e => pure (True, !(f acc' e))

-- --------------------------------------------------------------------------

