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


public export %inline read: HasIO io => {t:Type} -> DecEq t => IOHashSet t -> t -> IO Bool
read hs k = runIOHashSet hs.table k (pure . Left . isJust)

public export %inline write: HasIO io => {t:Type} -> DecEq t => IOHashSet t -> t -> IO Bool
write hs k = runIOHashSet hs.table k (\x => pure $ Right (isJust x, Just k))

public export %inline delete: HasIO io => {t:Type} -> DecEq t => IOHashSet t -> t -> IO Bool
delete hs k = runIOHashSet hs.table k (\x => pure $ Right (isJust x, Nothing))

