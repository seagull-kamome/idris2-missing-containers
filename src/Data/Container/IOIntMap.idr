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
  {f:Int -> Type} -> IODIntMap f -> (i:Int) -> io (Maybe (f i))
read arr i = lookup arr.hashmap i


public export write : HasIO io =>
  {f:Int -> Type} -> IODIntMap f -> (i:Int) -> (v:f i) ->
  io (Maybe (f i))
write arr i v = modify arr.hashmap i (\x => pure (x, Just v))


public export remove : HasIO io =>
  {f:Int -> Type} -> IODIntMap f -> (i:Int) -> io (Maybe (f i))
remove arr i = remove arr.hashmap i


