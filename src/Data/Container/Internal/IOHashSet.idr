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


public export newIOHashSet':
  {0 tk:Type} -> (hashfunc: tk -> Bits32) ->
  IO (IOHashSet' tk t)
newIOHashSet' hashfunc =
  pure $ MkIOHashSet {
    hashfunc = hashfunc,
    root = !(primIO $ prim__newArray L0Width Nothing) }


public export
data HashSetAction : Type -> Type -> Type where
  NoOp : r -> HashSetAction r t
  Remove : r -> HashSetAction r t
  InsertOrReplace : r -> t -> HashSetAction r t


||| IOHashSet の要素を検索し、削除,更新捜査を行います。
|||
||| @k Search key
||| @notfound
||| @found 検索結果を受け取り、その後の処理方を返すコールバック関数
||| @hs Target HashSet
public export runIOHashSet : {0 r:Type} ->
  {0 tk:Type} -> {0 t:Type} ->
  IsHashSet' (IOHashSet' tk t) tk t =>
  (hs:IOHashSet' tk t) ->
  (k:tk) ->
  (notfound:IO (HashSetAction r t)) ->
  (found:(x:t ** k = (keyfunc hs x)) -> IO (HashSetAction r t)) ->
  IO r
runIOHashSet hs k notfound found  = do
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
      case !(notfound) of
        NoOp r => pure r
        Remove r => pure r
        InsertOrReplace r v => do
          l1arr <- primIO $ prim__newArray L1Width []
          primIO $ prim__arraySet l1arr ix1 [v]
          primIO $ prim__arraySet hs.root ix0 (Just l1arr)
          pure r
  where
    replaceL2 : List t -> IO (r, Maybe (List t))
    replaceL2 [] = do
      case !(notfound) of
        NoOp r => pure (r, Nothing)                -- NoOpr
        Remove r => pure (r, Nothing)              -- Remove
        InsertOrReplace r v  => pure (r, Just [v]) -- InsertOrUpdate
    replaceL2 xs@(x::xs') with (decEq k (keyfunc hs x))
      _ | Yes prf = case !(found (x ** prf)) of
        NoOp r => pure (r, Nothing)
        Remove r => pure (r, Just xs')
        InsertOrReplace r v => pure (r, Just (v::xs'))
      _ | No _ = do
          (r, Just zs) <- replaceL2 xs'
            | r@(_, Nothing) => pure r
          pure (r, Just (x::zs))


-- --------------------------------------------------------------------------

public export updateIOHashSet:
  {0 tk:Type} -> {0 t:Type} ->
  IsHashSet' (IOHashSet' tk t) tk t =>
  (hs:IOHashSet' tk t) ->
  (visit: (orig:t) -> IO ((new:t ** keyfunc hs orig = keyfunc hs new))) ->
  IO ()
updateIOHashSet hs visit = for_ [0..(L0Width - 1)] $ \ix0 => do
  Just l1arr <- primIO $ prim__arrayGet hs.root ix0
    | Nothing => pure ()
  for_ [0..(L1Width - 1)] $ \ix1 => do
    primIO $ prim__arraySet l1arr ix1
       !(for !(primIO $ prim__arrayGet l1arr ix1)
              $ \x => pure $ fst !(visit x))

-- --------------------------------------------------------------------------

public export clear: (hs:IOHashSet' tk t) -> IO ()
clear hs = for_ [0..(L0Width - 1)] $ \ix =>
  primIO $ prim__arraySet hs.root ix Nothing


-- --------------------------------------------------------------------------

public export filterIOHashSet:
  {0 tk:Type} -> {0 t:Type} ->
  IsHashSet' (IOHashSet' tk t) tk t =>
  (hs:IOHashSet' tk t) -> (pred: t -> IO Bool) -> IO ()
filterIOHashSet hs pred = for_ [0..L0Width] $ \ix0 => do
  Just l1arr <- primIO $ prim__arrayGet hs.root ix0
    | Nothing => pure ()
  for_ [0..L1Width] $ \ix1 =>
    primIO $ prim__arraySet l1arr ix1
      !(foldlM (\acc, e => pure $ if !(pred e) then (e::acc) else acc) []
              !(primIO $ prim__arrayGet l1arr ix1) )

-- --------------------------------------------------------------------------

public export foldIOHashSet:
  {0 tk:Type} -> {0 t:Type} ->
  (hs:IOHashSet' tk t) ->
  (visit:acc -> t -> IO (Bool, acc)) -> acc -> IO acc
foldIOHashSet hs visit x = loop0 L0Width x
  where
    loop2: List t -> acc -> IO (Bool, acc)
    loop2 [] x = pure (True, x)
    loop2 (y::ys) x = do
      (True, x') <- visit x y | (_, x') => pure (False, x')
      loop2 ys x'

    loop1: ArrayData (List t) -> Int -> acc -> IO (Bool, acc)
    loop1 _ 0 x = pure (True, x)
    loop1 l1arr ix1 x = do
        let ix = ix1 - 1
        ys <- primIO $ prim__arrayGet l1arr ix
        (True, x') <- loop2 ys x | (_, x') => pure (False, x')
        assert_total $ loop1 l1arr ix1 x'

    loop0: Int -> acc -> IO acc
    loop0 0 x = pure x
    loop0 ix0 x = do
        let ix = ix0 - 1
        Just l1arr <- primIO $ prim__arrayGet hs.root ix
          | Nothing => assert_total $ loop0 ix x
        (True, x') <- loop1 l1arr L1Width x | (_, x') => pure x'
        assert_total $ loop0 ix x'

public export %inline count:
  (hs:IOHashSet' tk t) -> IO Int
count hs = foldIOHashSet hs (\acc, _ => pure (True, acc + 1)) 0


public export %inline keyList:
 IsHashSet' (IOHashSet' tk t) tk t => (hs:IOHashSet' tk t) -> IO (List tk)
keyList hs = foldIOHashSet hs (\acc, x => pure (True, keyfunc hs x::acc)) []


public export %inline toList: (hs:IOHashSet' tk t) -> IO (List t)
toList hs = foldIOHashSet hs (\acc, x => pure (True, x::acc)) []


-- --------------------------------------------------------------------------
