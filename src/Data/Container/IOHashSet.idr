module Data.Container.IOHashSet

import Data.Maybe
import Decidable.Equality
import Data.Hashable

import public Data.Container.Internal.IOHashSet

%default total

-- --------------------------------------------------------------------------

public export IOHashSet : Type -> Type
IOHashSet t = IOHashSet' t t

DecEq t => IsHashSet' (IOHashSet t) t t where
  keyfunc _ = id

public export %inline newIOHashSet : HasIO io => Hashable t => DecEq t =>
 io (IOHashSet t)
newIOHashSet = newIOHashSet' (cast . hash)


public export %inline lookup: HasIO io => {t:Type} -> DecEq t => IOHashSet t -> t -> IO Bool
lookup hs k = runIOHashSet hs k (pure . Left . isJust)

public export %inline insert: HasIO io => {t:Type} -> DecEq t => IOHashSet t -> t -> IO Bool
insert hs k = runIOHashSet hs k (\x => pure $ Right (isJust x, Just k))

public export %inline remove: HasIO io => {t:Type} -> DecEq t => IOHashSet t -> t -> IO Bool
remove hs k = runIOHashSet hs k (\x => pure $ Right (isJust x, Nothing))

