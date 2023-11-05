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

public export %inline newIODIntMap: HasIO io => {f:Int -> Type} -> io (IODIntMap f)
newIODIntMap = pure $ MkIODIntMap $ !(newIODHashMap' cast)


public export %inline read: HasIO io =>
  {f:Int -> Type} -> IODIntMap f -> (i:Int) -> io (Maybe (f i))
read im i = read im.table i

public export %inline write: HasIO io =>
  {f:Int -> Type} -> IODIntMap f -> (i:Int) -> (v:f i) -> io (Maybe (f i))
write im i v = write im.table i v


public export %inline delete: HasIO io =>
  {f:Int -> Type} -> IODIntMap f -> (i:Int) -> io (Maybe (f i))
delete im i = delete im.table i


public export %inline update: {f:Int -> Type} -> HasIO io =>
  IODIntMap f -> (i:Int) -> (g:Maybe (f i) -> io (r, (Maybe (f i)))) -> io r
update im i g = update im.table i g


-- --------------------------------------------------------------------------

public export %inline IOIntMap: Type -> Type
IOIntMap tv = IODIntMap (const tv)

public export %inline newIOIntMap: HasIO io => (t:Type) -> io (IOIntMap t)
newIOIntMap {t=t} = newIODIntMap {f=const t}

