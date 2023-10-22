module Data.Container.IODArray

import Data.IOArray.Prims
import Data.So

%default total


-- --------------------------------------------------------------------------

namespace FixedSize

  export
  record IODArray (0 size:Int) (0 f:Int -> Type) where
    constructor MkIODArray
    arraydata: ArrayData (Maybe ())

  export IOArray : Int -> Type -> Type
  IOArray size ty = IODArray size (const ty)



  public export newIODArray : HasIO io => {f:Int -> Type} -> {size:Int} -> io (IODArray size f)
  newIODArray {size=size} = pure $ MkIODArray !(primIO $ prim__newArray size Nothing)

  public export writeIODArray : HasIO io =>
    {f: Int -> Type} -> (i:Int) -> (f i) -> IODArray size f ->
    {0 prf: So (i >= 0 && i < size)} ->
    io ()
  writeIODArray i v arr = primIO $ prim__arraySet arr.arraydata i (believe_me $ Just v)

  public export readIODArray : HasIO io =>
    {f: Int -> Type} -> (i:Int) -> IODArray size f ->
    {0 prf: So (i >= 0 && i < size)} ->
    io (Maybe (f i))
  readIODArray i arr = primIO (prim__arrayGet arr.arraydata i) >>= pure . believe_me

  public export size : {size:Int} -> IODArray size f -> Int
  size {size=x} _ = x


  -- TODO: copy, remove



-- --------------------------------------------------------------------------

namespace VariableSize

  export
  record IODArray (0 f:Int -> Type) where
    constructor MkIODArray
    size: Int
    arraydata: ArrayData (Maybe ())

  export IOArray : Type -> Type
  IOArray ty = IODArray (const ty)



  public export newIODArray : HasIO io => {f:Int -> Type} -> {size:Int} -> io (IODArray f)
  newIODArray {size=size} = pure $ MkIODArray size !(primIO $ prim__newArray size Nothing)

  public export writeIODArray : HasIO io =>
    {f: Int -> Type} -> (i:Int) -> (f i) -> (arr:IODArray f) ->
    {0 prf: So (i >= 0 && i < arr.size)} ->
    io ()
  writeIODArray i v arr = primIO $ prim__arraySet arr.arraydata i (believe_me $ Just v)

  public export readIODArray : HasIO io =>
    {f: Int -> Type} -> (i:Int) -> (arr:IODArray f) ->
    {0 prf: So (i >= 0 && i < arr.size)} ->
    io (Maybe (f i))
  readIODArray i arr = primIO (prim__arrayGet arr.arraydata i) >>= pure . believe_me

  public export size : IODArray f -> Int
  size arr = arr.size


  -- TODO: copy, remove, resize



