module Data.Container.IOHashMap

import public Data.Container.Internal.IOHashSet

import Decidable.Equality
import Data.List
import Data.Maybe
import Data.Hashable
import Data.IOArray.Prims

%default total

-- --------------------------------------------------------------------------
-- Deriving IODHashMap from IOHashSet
namespace IODHashMap
  ||| Mutable Dependent Type HashMap
  ||| @tk is type of key
  ||| @tv is type of value that dended to key value.
  public export %inline IODHashMap : (tk:Type) -> (tv:tk -> Type) -> Type
  IODHashMap tk tv = IOHashSet' tk (k:tk ** tv k)

  %inline
  DecEq tk => IsHashSet' (IODHashMap tk tv) tk (k:tk ** tv k) where
    keyfunc _ = fst


  ||| Create new IODHashMap with specified hash function.
  ||| @hf is hash function to calc. hash value of key.
  public export %inline newIODHashMap' : HasIO io => DecEq tk =>
    (hf:tk -> Bits32) -> io (IODHashMap tk tv)
  newIODHashMap' hf = newIOHashSet' {tk=tk} hf

  ||| Create new IODHashMap with default hash function
  ||| The key type must impliments Hashable interface.
  public export %inline newIODHashMap : HasIO io => Hashable tk => DecEq tk =>
    io (IODHashMap tk tv)
  newIODHashMap = newIODHashMap' (cast . hash)


  ||| Insert key-value pair into HashMap
  ||| @k is the key
  ||| @v is the value
  ||| @retval Nothing means the key-value pair has inserted.
  ||| @retval Just x means HashMap already has the key for value x,
  |||   and it has replaced now.
  public export insert: HasIO io =>
    {tk:Type} -> DecEq tk => {tv:tk -> Type} -> IODHashMap tk tv -> (k:tk) -> (v:tv k) ->
    io (Maybe (tv k))
  insert hm k v = runIOHashSet hm k go where
    go : Maybe (x ** (k = keyfunc hm x)) ->
        io (Either (Maybe (tv k)) (Maybe (tv k), Maybe (k:tk ** tv k)))
    go Nothing           = pure $ Right (Nothing, Just (k ** v))
    go (Just (x ** prf)) = pure $ Right $ rewrite prf in (Just x.snd, Just (k ** v))


  ||| Lookup the HashMap
  ||| @k is the key
  ||| @retval Nothing means the key not found.
  ||| @retval Just x means found the key and x is an assosiate value.
  public export lookup: HasIO io =>
    {tk:Type} -> DecEq tk => {tv:tk -> Type} -> IODHashMap tk tv -> (k:tk) ->
    io (Maybe (tv k))
  lookup hm k = runIOHashSet hm k go where
    go : Maybe (x ** (k = keyfunc hm x)) ->
        io (Either (Maybe (tv k)) (Maybe (tv k), Maybe (k:tk ** tv k)))
    go Nothing           = pure $ Left Nothing
    go (Just (x ** prf)) = pure $ Left $ Just $ rewrite prf in x.snd


  ||| Remove key-value pair from HashMap
  |||
  |||
  public export remove: HasIO io =>
    {tk:Type} -> DecEq tk => {tv:tk -> Type} -> IODHashMap tk tv -> (k:tk) ->
    io (Maybe (tv k))
  remove hm k = runIOHashSet hm k go where
    go : Maybe (x ** (k = keyfunc hm x)) ->
        io (Either (Maybe (tv k)) (Maybe (tv k), Maybe (k:tk ** tv k)))
    go Nothing           = pure $ Left Nothing
    go (Just (x ** prf)) = pure $ Right $ rewrite prf in (Just x.snd, Nothing)

  |||
  |||
  |||
  public export modify: HasIO io =>
    {tk:Type} -> DecEq tk => {tv:tk -> Type} -> IODHashMap tk tv -> (k:tk) ->
    (Maybe (tv k) -> io (tr, Maybe (tv k))) ->
    io tr
  modify hm k g = runIOHashSet hm k go where
    go : Maybe (x ** (k = keyfunc hm x)) ->
        io (Either tr (tr, Maybe (k:tk ** tv k)))
    go Nothing           = pure $ case !(g Nothing) of
      (r, Nothing) => Left r
      (r, Just v') => Right (r, Just (k ** v'))
    go (Just (x ** prf)) = pure $ case !(g (Just $ rewrite prf in x.snd)) of
      (r, Nothing) => Right (r, Nothing)
      (r, Just v') => Right (r, Just (k ** v'))


-- --------------------------------------------------------------------------
-- Deriving IOHashMap from IODHashMap
namespace IOHashMap

  public export %inline IOHashMap : (tk:Type) -> (tv:Type) -> Type
  IOHashMap tk tv = IODHashMap tk (const tv)

  public export %inline newIOHashMap' : HasIO io => DecEq tk =>
    (hf:tk -> Bits32) -> io (IOHashMap tk tv)
  newIOHashMap' = newIODHashMap'

  public export %inline newIOHashMap : HasIO io => Hashable tk => DecEq tk =>
    io (IOHashMap tk tv)
  newIOHashMap = newIODHashMap

