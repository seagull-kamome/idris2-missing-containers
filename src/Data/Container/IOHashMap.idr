-- Implimentation of mutable dependent and independent type hash map.
-- 
-- Copyright 2023, HATTORI, Hiroki
-- This file is released under the MIT license, see LICENSE for more detail.  
--
module Data.Container.IOHashMap

import Data.Container.Internal.IOHashSet

import Decidable.Equality
import Data.List
import Data.Maybe
import Data.IOArray.Prims
import Data.Hash.Algorithm
-- import Data.List.Lazy {- package:contrib -}

%default total

-- --------------------------------------------------------------------------
-- Deriving IODHashMap from IOHashSet

||| Mutable Dependent Type HashMap
||| @tk is type of key
||| @tv is type of value that depended to key value.
export
record IODHashMap (tk:Type) (tv:tk -> Type) where
  constructor MkIODHashMap
  table: IOHashSet' tk (k:tk ** tv k)

%inline
{0 tv:tk -> Type} -> DecEq tk =>
  IsHashSet' (IOHashSet' tk (k:tk ** tv k)) tk (k:tk ** tv k) where
  keyfunc _ = fst


||| Create new IODHashMap with specified hash function.
||| @hf is hash function to calc. hash value of key.
public export %inline newIODHashMap : HasIO io => DecEq tk =>
  (hf:tk -> Bits32) -> io (IODHashMap tk tv)
newIODHashMap hf = pure $ MkIODHashMap !(newIOHashSet' {tk=tk} hf)


-- public export %inline newIODHashMap :
--   HasIO io => DecEq tk =>
--   HashAlgorithm algo crypt Bits32 =>
--   Hashable tk =>
--   algo -> io (IODHashMap tk tv)
-- newIODHashMap seed = newIODHashMap' (\x => finalize $ hash x seed)


||| Insert key-value pair into HashMap
||| @k is the key
||| @v is the value
||| @retval Nothing means the key-value pair has inserted.
||| @retval Just x means HashMap already has the key for value x,
|||   and it has replaced now.
public export write: HasIO io =>
  {0 tk:Type} -> DecEq tk => {0 tv:tk -> Type} -> IODHashMap tk tv -> (k:tk) -> (v:tv k) ->
  io (Maybe (tv k))
write hm k v = runIOHashSet hm.table k go where
  go : Maybe (x ** (k = keyfunc hm.table x)) ->
      io (Either (Maybe (tv k)) (Maybe (tv k), Maybe (k:tk ** tv k)))
  go Nothing           = pure $ Right (Nothing, Just (k ** v))
  go (Just (x ** prf)) = pure $ Right $ rewrite prf in (Just x.snd, Just (k ** v))


||| Lookup the HashMap
||| @k is the key
||| @retval Nothing means the key not found.
||| @retval Just x means found the key and x is an assosiate value.
public export read: HasIO io =>
  {0 tk:Type} -> DecEq tk => {0 tv:tk -> Type} -> IODHashMap tk tv -> (k:tk) ->
  io (Maybe (tv k))
read hm k = runIOHashSet hm.table k go where
  go : Maybe (x ** (k = keyfunc hm.table x)) ->
      io (Either (Maybe (tv k)) (Maybe (tv k), Maybe (k:tk ** tv k)))
  go Nothing           = pure $ Left Nothing
  go (Just (x ** prf)) = pure $ Left $ Just $ rewrite prf in x.snd


||| Remove key-value pair from HashMap
|||
|||
public export delete: HasIO io =>
  {0 tk:Type} -> DecEq tk => {0 tv:tk -> Type} -> IODHashMap tk tv -> (k:tk) ->
    io (Maybe (tv k))
delete hm k = runIOHashSet hm.table k go where
  go : Maybe (x ** (k = keyfunc hm.table x)) ->
      io (Either (Maybe (tv k)) (Maybe (tv k), Maybe (k:tk ** tv k)))
  go Nothing           = pure $ Left Nothing
  go (Just (x ** prf)) = pure $ Right $ rewrite prf in (Just x.snd, Nothing)

|||
|||
|||
public export update: HasIO io =>
  {0 tk:Type} -> DecEq tk => {0 tv:tk -> Type} -> IODHashMap tk tv -> (k:tk) ->
  (Maybe (tv k) -> io (tr, Maybe (tv k))) ->
  io tr
update hm k g = runIOHashSet hm.table k go where
  go : Maybe (x ** (k = keyfunc hm.table x)) ->
      io (Either tr (tr, Maybe (k:tk ** tv k)))
  go Nothing           = pure $ case !(g Nothing) of
    (r, Nothing) => Left r
    (r, Just v') => Right (r, Just (k ** v'))
  go (Just (x ** prf)) = pure $ case !(g (Just $ rewrite prf in x.snd)) of
    (r, Nothing) => Right (r, Nothing)
    (r, Just v') => Right (r, Just (k ** v'))


||| Update all elements of HashMap
||| @hm is the HashMap
||| @f is maping function
public export updateAll: HasIO io => DecEq tk =>
  IODHashMap tk tv -> (f:(k:tk) -> (tv k) -> io (tv k)) -> io ()
updateAll hm f = updateIOHashSet hm.table $ \x =>
  pure ((fst x ** !(f (fst x) (snd x))) ** Refl)



||| Make the HashMap Empry.
public export clear: HasIO io => IODHashMap tk tv -> io ()
clear hm = clear hm.table


||| Number of elements.
public export %inline count: HasIO io => IODHashMap tk tv -> io Int
count hm = count hm.table


||| List of keys.
public export %inline keyList: HasIO io =>
  {0 tk:Type} -> DecEq tk => {0 tv:tk -> Type} -> IODHashMap tk tv -> io (List tk)
keyList hm = keyList hm.table


||| List of elements.
public export %inline toList: HasIO io => IODHashMap tk tv -> io (List (k:tk ** tv k))
toList hm = toList hm.table


-- public export %inline toList: HasIO io =>
--   IODHashMap tk tv -> io (LazyList (k:tk ** tv k))

-- private read': HasIO io => DecEq tk => {0 tv:tk -> Type} ->
--   IODHashMap tk tv -> (k:tk ** tv k) -> IO Bool
-- read' hm x = read hm (keyfunc hm.table x) >>= pure . isJust


public export %inline union: HasIO io =>
  {0 tk:Type} -> DecEq tk => {0 tv:tk -> Type} ->
  IODHashMap tk tv -> IODHashMap tk tv -> io ()
union lhs rhs = foldIOHashSet rhs.table (\acc, x =>
  write lhs (fst x) (snd x) >>= \_ => pure (True, ())) ()


public export %inline intersect: HasIO io =>
  {0 tk:Type} -> DecEq tk => {0 tv, tv':tk -> Type} ->
  IODHashMap tk tv -> IODHashMap tk tv' -> io ()
intersect lhs rhs = filterIOHashSet lhs.table $
  \e => pure $ isJust !(read rhs (keyfunc lhs.table e))


public export %inline except: HasIO io =>
  {0 tk:Type} -> DecEq tk => {0 tv, tv':tk -> Type} ->
  IODHashMap tk tv -> IODHashMap tk tv' -> io ()
except lhs rhs = filterIOHashSet lhs.table $
  \e => pure $ isNothing !(read rhs (keyfunc lhs.table e))


||| fold all elements into single value.
||| @f is accumulate function.
||| @acc is initial accumulator value.]
public export %inline fold: HasIO io =>
  {0 tk:Type} -> DecEq tk => {0 tv:tk -> Type} ->
  IODHashMap tk tv -> (f:acc -> (k:tk ** tv k) -> io acc) -> acc -> io acc
fold hm f = foldIOHashSet hm.table $ \acc', e => pure (True, !(f acc' e))




-- --------------------------------------------------------------------------
-- Deriving IOHashMap from IODHashMap

public export %inline IOHashMap : (tk:Type) -> (tv:Type) -> Type
IOHashMap tk tv = IODHashMap tk (const tv)

public export %inline newIOHashMap : HasIO io => DecEq tk =>
  (hf:tk -> Bits32) -> io (IOHashMap tk tv)
newIOHashMap = newIODHashMap

-- public export %inline newIOHashMap : HasIO io => Hashable tk => DecEq tk =>
--   io (IOHashMap tk tv)
-- newIOHashMap = newIODHashMap

