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

public export %inline newIODIntMap: HasIO io => {0 f:Int -> Type} -> io (IODIntMap f)
newIODIntMap = pure $ MkIODIntMap $ !(newIODHashMap cast)


public export %inline read: HasIO io =>
  {0 f:Int -> Type} -> IODIntMap f -> (i:Int) -> io (Maybe (f i))
read im i = read im.table i

public export %inline write: HasIO io =>
  {0 f:Int -> Type} -> IODIntMap f -> (i:Int) -> (v:f i) -> io (Maybe (f i))
write im i v = write im.table i v


public export %inline delete: HasIO io =>
  {0 f:Int -> Type} -> IODIntMap f -> (i:Int) -> io (Maybe (f i))
delete im i = delete im.table i


public export %inline update: {0 f:Int -> Type} -> HasIO io =>
  IODIntMap f -> (i:Int) -> (g:Maybe (f i) -> io (r, (Maybe (f i)))) -> io r
update im i g = update im.table i g


public export %inline updateAll: HasIO io => {0 f:Int -> Type} ->
  IODIntMap f -> (g:(k:Int) -> f k -> io (f k)) -> io ()
updateAll im g = updateAll im.table g

public export %inline clear: HasIO io => IODIntMap f -> io ()
clear im = clear im.table

public export %inline count: HasIO io => IODIntMap f -> io Int
count im = count im.table

public export %inline keyList: HasIO io => IODIntMap f -> io (List Int)
keyList im = keyList im.table

public export %inline toList: HasIO io => IODIntMap f -> io (List (k:Int ** f k))
toList im = toList im.table

public export %inline union: HasIO io => IODIntMap f -> IODIntMap f -> io ()
union lhs rhs = union lhs.table rhs.table

public export %inline intersect: HasIO io => IODIntMap f -> IODIntMap g -> io ()
intersect lhs rhs = intersect lhs.table rhs.table

public export %inline except: HasIO io => IODIntMap f -> IODIntMap g -> io ()
except lhs rhs = intersect lhs.table rhs.table


public export %inline fold: HasIO io => {0 f:Int -> Type} -> IODIntMap f ->
  (g:acc -> (i:Int ** f i) -> io acc) -> acc -> io acc
fold im = fold im.table


-- --------------------------------------------------------------------------

public export %inline IOIntMap: Type -> Type
IOIntMap tv = IODIntMap (const tv)

public export %inline newIOIntMap: HasIO io => (t:Type) -> io (IOIntMap t)
newIOIntMap {t=t} = newIODIntMap {f=const t}

