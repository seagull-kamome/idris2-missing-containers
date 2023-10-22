module Data.Container.IOHashMap

import Decidable.Equality
import Data.List
import Data.Maybe
import Data.Hashable
import Data.IOArray.Prims


%default total


-- --------------------------------------------------------------------------

L1Type : Type -> Int -> Type
L1Type _ 0 = Int
L1Type ty _ = ty

L0Width, L1Width : Int
L0Width = 1024
L1Width = 128


||| Mutable HashMap with user hash function and dependent type.
export
record IODHashMap (tk:Type) (tv:tk -> Type) where
  constructor MkIODIntMap
  hashfunc: tk -> Bits32
  root: ArrayData (Maybe $ ArrayData (List (k:tk ** tv k)))


||| Mutable HashMap with user hash function.
public export IOHashMap : Type -> Type -> Type
IOHashMap tk tv = IODHashMap tk (const tv)



||| Create empty IODHashMap with specific hash function.
public export newIODHashMap' : HasIO io =>
  {tk:Type} -> {tv:tk -> Type} ->
  (hf:tk -> Bits32) -> io (IODHashMap tk tv)
newIODHashMap' hf = pure $ MkIODIntMap {
  hashfunc = hf,
  root = !(primIO $ prim__newArray L0Width Nothing) }



||| Create empty IODHashMap
public export newIODHashMap : HasIO io =>
  {tk:Type} -> Hashable tk => Eq tk => {tv:tk -> Type} -> io (IODHashMap tk tv)
newIODHashMap = newIODHashMap' (the Bits32 . cast . hash)




||| IODHashMap の要素を検索し、削除,更新捜査を行います。
|||
||| @k Search key
||| @g 検索結果を受け取り、その後の処理方を返すコールバック関数
||| @hm Target HashMap
export
runIODHashMap : HasIO io => {0 r:Type} ->
  {tk:Type} -> DecEq tk => {tv:tk -> Type} ->
  (k:tk) -> (g:Maybe (tv k) -> io (Either r (r, Maybe (tv k)))) ->
  (hm:IODHashMap tk tv) -> io r
runIODHashMap k g hm = do
  let h = the Int $ cast $ hm.hashfunc k
  let ix0 = (h `div` L1Width) `mod` L0Width -- Index to L0
  let ix1 = h `mod` L1Width                 -- Index to L1
  --
  case !(primIO $ prim__arrayGet hm.root ix0) of
    -- L0 にエントリがあった場合
    Just l1arr => do
      case !((primIO $ prim__arrayGet l1arr ix1) >>= replaceL2) of
        (r, Nothing) => pure r -- 変化無し
        (r, Just []) => do     -- 削除の結果L2が空になった
          l1size <- foldlM
            (\n, i => pure $ if null !(primIO $ prim__arrayGet l1arr i)
                                then n else (n + 1))
            0 [0..(L1Width - 1)]
          if l1size <= 1
            then primIO $ prim__arraySet hm.root ix0 Nothing -- l1も空になったのでL0から削除
            else do
              primIO $ prim__arraySet l1arr ix1 []
              primIO $ prim__arraySet hm.root ix0 (Just l1arr)
          pure r
        (r, Just ys) => do -- L1が更新された
          primIO $ prim__arraySet l1arr ix1 ys
          pure r
    --
    -- L0にエントリがなかった
    Nothing => do
      case !(g Nothing) of
        Left r => pure r
        Right (r, Nothing) => pure r
        Right (r, Just v) => do       -- InsertOrUpdate
          l1arr <- primIO $ prim__newArray L1Width []
          primIO $ prim__arraySet l1arr ix1 [(k ** v)]
          primIO $ prim__arraySet hm.root ix0 (Just l1arr)
          pure r
  where
    replaceL2 : List (k:tk ** tv k) -> io (r, Maybe (List (k:tk ** tv k)))
    replaceL2 [] = do
      case !(g Nothing) of
        Left r => pure (r, Nothing)                     -- NoOpr
        Right (r, Nothing) => pure (r, Nothing)         -- Remove
        Right (r, Just v)  => pure (r, Just [(k ** v)]) -- InsertOrUpdate
    replaceL2 xs@(x@(k' ** v)::xs') with (decEq k k')
      _ | Yes prf = case !(g (Just $ rewrite prf in v)) of -- Found!
        Left r => pure (r, Nothing)
        Right (r, Nothing) => pure (r, Just xs')
        Right (r, Just y') => pure (r, Just ((k ** y')::xs'))
      _ | No _ = do
          (r, Just zs) <- replaceL2 xs'
            | r@(_, Nothing) => pure r
          pure (r, Just (x::zs))


||| Lookup an element from HashMap
||| @k Search key
||| @hm Target HashMap
public export lookup : HasIO io =>
  {tk:Type} -> DecEq tk => {tv:tk -> Type} ->
  (k:tk) -> (hm:IODHashMap tk tv) -> io (Maybe (tv k))
lookup k hm = runIODHashMap k (pure . Left) hm


||| Insert an element to HashMap
||| @k Search key
||| @v The value to insert.
||| @hm Target HashMap
public export insert : HasIO io =>
  {tk:Type} -> DecEq tk => {tv:tk -> Type} ->
  (k:tk) -> (v:tv k) -> (hm:IODHashMap tk tv) -> io (Maybe (tv k))
insert k v arr = runIODHashMap k (\x => pure $ Right (x, Just v)) arr


||| Modify an element of HashMap
||| @k Search key
||| @g Callback function
||| @hm Target HashMap
public export modify : HasIO io => 
  {tk:Type} -> DecEq tk => {tv:tk -> Type} ->
  (k:tk) -> (g:Maybe (tv k) -> io (r, Maybe (tv k))) ->
  (hm:IODHashMap tk tv) -> io r
modify k g hm = runIODHashMap k (\x => g x >>= pure . Right) hm



||| Remove an element from HashMap
||| @k Search key
||| @hm Target HashMap
public export remove : HasIO io =>
  {tk:Type} -> DecEq tk => {tv:tk -> Type} ->
  (k:tk) -> (hm:IODHashMap tk tv) -> io (Maybe (tv k))
remove k arr = runIODHashMap k (\x => pure $ Right (x, Nothing)) arr


