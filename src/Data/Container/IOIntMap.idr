module Data.Container.IOIntMap

import Decidable.Equality

import Data.Container.IOHashMap

%default total

-- --------------------------------------------------------------------------

export
record IODIntMap (f:Int -> Type) where
  constructor MkIODIntMap
  hashmap: IODHashMap Int f

export IOIntMap : Type -> Type
IOIntMap tv = IODIntMap (const tv)


public export newIODIntMap : HasIO io => {f:Int -> Type} -> io (IODIntMap f)
newIODIntMap = pure $ MkIODIntMap !(newIODHashMap' cast)


public export read : HasIO io =>
  (i:Int) -> {f:Int -> Type} -> IODIntMap f -> io (Maybe (f i))
read i arr = lookup i arr.hashmap


public export write : HasIO io =>
  (i:Int) -> {f:Int -> Type} -> (v:f i) -> IODIntMap f -> io (Maybe (f i))
write i v arr = modify i (\x => pure (x, Just v)) arr.hashmap


public export remove : HasIO io =>
  (i:Int) -> {f:Int -> Type} -> IODIntMap f -> io (Maybe (f i))
remove i arr = remove i arr.hashmap


