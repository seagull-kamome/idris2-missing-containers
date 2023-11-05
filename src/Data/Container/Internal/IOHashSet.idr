-- Internal implimentations of sparse array based containers.
-- 
-- Copyright 2023, HATTORI, Hiroki
-- This file is released under the MIT license, see LICENSE for more detail.  
--
module Data.Container.Internal.IOHashSet

import Decidable.Equality
import Data.IOArray.Prims
import Data.Maybe
import Data.List


%default total

-- --------------------------------------------------------------------------
-- Configuration

L1Type : Type -> Int -> Type
L1Type _ 0 = Int
L1Type ty _ = ty

L0Width, L1Width : Int
L0Width = 1024
L1Width = 128

-- --------------------------------------------------------------------------

public export
record IOHashSet' (tk:Type) (t:Type) where
  constructor MkIOHashSet
  hashfunc: tk -> Bits32
  root: ArrayData (Maybe $ ArrayData (List t))


public export
interface DecEq tk => IsHashSet' t tk tv | t where
  %inline keyfunc: (0 hs:t) -> tv -> tk


public export newIOHashSet': HasIO io =>
  {0 tk:Type} -> (hashfunc: tk -> Bits32) ->
  io (IOHashSet' tk t)
newIOHashSet' hashfunc =
  pure $ MkIOHashSet {
    hashfunc = hashfunc,
    root = !(primIO $ prim__newArray L0Width Nothing) }


||| IOHashSet の要素を検索し、削除,更新捜査を行います。
|||
||| @k Search key
||| @g 検索結果を受け取り、その後の処理方を返すコールバック関数
||| @hs Target HashSet
public export
runIOHashSet : HasIO io => {0 r:Type} ->
  {0 tk:Type} -> {0 t:Type} ->
  IsHashSet' (IOHashSet' tk t) tk t =>
  (hs:IOHashSet' tk t) ->
  (k:tk) ->
  (g:Maybe (x:t ** k = (keyfunc hs x)) -> io (Either r (r, Maybe t))) ->
  io r
runIOHashSet hs k g = do
  let h = the Int $ cast $ hs.hashfunc k
  let ix0 = (h `div` L1Width) `mod` L0Width -- Index to L0
  let ix1 = h `mod` L1Width                 -- Index to L1
  --
  case !(primIO $ prim__arrayGet hs.root ix0) of
    -- Found on L0
    Just l1arr => do
      case !((primIO $ prim__arrayGet l1arr ix1) >>= replaceL2) of
        (r, Nothing) => pure r -- No changes
        (r, Just []) => do     -- It becomes empty
          l1size <- foldlM
            (\n, i => pure $ if null !(primIO $ prim__arrayGet l1arr i)
                                then n else (n + 1))
            0 [0..(L1Width - 1)]
          if l1size <= 1
            then primIO $ prim__arraySet hs.root ix0 Nothing -- l1も空になったのでL0から削除
            else do
              primIO $ prim__arraySet l1arr ix1 []
              primIO $ prim__arraySet hs.root ix0 (Just l1arr)
          pure r
        (r, Just ys) => do -- L1 has updated
          primIO $ prim__arraySet l1arr ix1 ys
          pure r
    --
    -- No entry found on L0
    Nothing => do
      case !(g Nothing) of
        Left r => pure r
        Right (r, Nothing) => pure r
        Right (r, Just v) => do       -- InsertOrUpdate
          l1arr <- primIO $ prim__newArray L1Width []
          primIO $ prim__arraySet l1arr ix1 [v]
          primIO $ prim__arraySet hs.root ix0 (Just l1arr)
          pure r
  where
    replaceL2 : List t -> io (r, Maybe (List t))
    replaceL2 [] = do
      case !(g Nothing) of
        Left r => pure (r, Nothing)                     -- NoOpr
        Right (r, Nothing) => pure (r, Nothing)         -- Remove
        Right (r, Just v)  => pure (r, Just [v]) -- InsertOrUpdate
    replaceL2 xs@(x::xs') with (decEq k (keyfunc hs x))
      _ | Yes prf = case !(g (Just (x ** prf))) of -- Found!
        Left r => pure (r, Nothing)
        Right (r, Nothing) => pure (r, Just xs')
        Right (r, Just v) => pure (r, Just (v::xs'))
      _ | No _ = do
          (r, Just zs) <- replaceL2 xs'
            | r@(_, Nothing) => pure r
          pure (r, Just (x::zs))

