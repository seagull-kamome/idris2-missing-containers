-- Implimentation of mutable dependent and independent type hash map.
--
-- Copyright 2023, HATTORI, Hiroki
-- This file is released under the MIT license, see LICENSE for more detail.
--
module Data.Container.IOHashSet

import Data.Maybe
import Decidable.Equality

import Data.Container.Internal.IOHashSet

%default total

-- --------------------------------------------------------------------------

export
record IOHashSet t where
  constructor MkIOHashSet
  table: IOHashSet' t t

%inline
DecEq t => IsHashSet' (IOHashSet' t t) t t where
  keyfunc _ = id

public export %inline newIOHashSet :
  DecEq t => (t -> Bits32) -> IO (IOHashSet t)
newIOHashSet hf = pure $ MkIOHashSet !(newIOHashSet' hf)


public export %inline read: DecEq t => IOHashSet t -> t -> IO Bool
read hs k = runIOHashSet hs.table k (pure $ NoOp False) (\_ => pure $ NoOp True)

public export %inline write: DecEq t => IOHashSet t -> t -> IO Bool
write hs k = runIOHashSet hs.table k (pure $ InsertOrReplace False k)
                                     (\_ => pure $ InsertOrReplace True k)

public export %inline delete: DecEq t => IOHashSet t -> t -> IO Bool
delete hs k = runIOHashSet hs.table k (pure $ Remove False)
                                      (\_ => pure $ Remove True)

public export %inline clear: IOHashSet t -> IO ()
clear hs = clear hs.table

public export %inline count: IOHashSet t -> IO Int
count hs = count hs.table

public export %inline toList: IOHashSet t -> IO (List t)
toList hs = toList hs.table

public export %inline union: DecEq t =>
  IOHashSet t -> IOHashSet t -> IO ()
union lhs rhs = foldIOHashSet rhs.table (\_, x =>
  write lhs x >>= \_ => pure (True, ())) ()

public export %inline intersect: DecEq t =>
  IOHashSet t -> IOHashSet t -> IO ()
intersect lhs rhs = filterIOHashSet lhs.table (read rhs)

public export %inline except: DecEq t =>
  IOHashSet t -> IOHashSet t -> IO ()
except lhs rhs = filterIOHashSet lhs.table (read rhs >=> pure . not)

public export %inline fold: DecEq t =>
  IOHashSet t -> (acc -> t -> IO acc) -> acc -> IO acc
fold hm f acc = foldIOHashSet hm.table (\acc', e => pure (True, !(f acc' e))) acc
