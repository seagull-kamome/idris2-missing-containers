-- Implimentation of mutable dependent and independent type map of Int.
--
-- Copyright 2023, HATTORI, Hiroki
-- This file is released under the MIT license, see LICENSE for more detail.
--
module Data.Container.IOIntMap

import Decidable.Equality
import Data.Container.IOHashMap

%default total

-- --------------------------------------------------------------------------

||| Mutable Dependent-Type IntMap
||| This is just a 'HashMap Int t' but hash function is 'id'.
||| @f is type of value that dependent to key value.
export
record IODIntMap (f:Int -> Type) where
  constructor MkIODIntMap
  table: IODHashMap Int f

public export %inline newIODIntMap: {0 f:Int -> Type} -> IO (IODIntMap f)
newIODIntMap = pure $ MkIODIntMap $ !(newIODHashMap cast)


public export %inline read: {0 f:Int -> Type} -> IODIntMap f -> (i:Int) -> IO (Maybe (f i))
read im i = read im.table i

public export %inline write: {0 f:Int -> Type} -> IODIntMap f -> (i:Int) -> (v:f i) -> IO (Maybe (f i))
write im i v = write im.table i v


public export %inline delete: {0 f:Int -> Type} -> IODIntMap f -> (i:Int) -> IO (Maybe (f i))
delete im i = delete im.table i


public export %inline update: {0 f:Int -> Type} ->
  IODIntMap f -> (i:Int) -> (g:Maybe (f i) -> IO (r, (Maybe (f i)))) -> IO r
update im i g = update im.table i g


public export %inline updateAll: {0 f:Int -> Type} ->
  IODIntMap f -> (g:(k:Int) -> f k -> IO (f k)) -> IO ()
updateAll im g = updateAll im.table g

public export %inline clear: IODIntMap f -> IO ()
clear im = clear im.table

public export %inline count: IODIntMap f -> IO Int
count im = count im.table

public export %inline keyList: IODIntMap f -> IO (List Int)
keyList im = keyList im.table

public export %inline toList: IODIntMap f -> IO (List (k:Int ** f k))
toList im = toList im.table

public export %inline union: IODIntMap f -> IODIntMap f -> IO ()
union lhs rhs = union lhs.table rhs.table

public export %inline intersect: IODIntMap f -> IODIntMap g -> IO ()
intersect lhs rhs = intersect lhs.table rhs.table

public export %inline except: IODIntMap f -> IODIntMap g -> IO ()
except lhs rhs = intersect lhs.table rhs.table


public export %inline fold: {0 f:Int -> Type} -> IODIntMap f ->
  (g:acc -> (i:Int ** f i) -> IO acc) -> acc -> IO acc
fold im = fold im.table


-- --------------------------------------------------------------------------

public export %inline IOIntMap: Type -> Type
IOIntMap tv = IODIntMap (const tv)

public export %inline newIOIntMap: (t:Type) -> IO (IOIntMap t)
newIOIntMap {t=t} = newIODIntMap {f=const t}
