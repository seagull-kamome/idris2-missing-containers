module Data.Container.Internal.Interface


%default total

-- --------------------------------------------------------------------------

namespace IODContainer

  interface IODContainer c tk tv | c where
    read : c -> (k:tk) -> IO (Maybe (tv k))
    write : c -> (k:tk) -> (tv k) -> IO (Maybe (tv k))
    update : c -> (k:tk) -> (tv k) -> IO (Maybe (tv k))
    delete : c -> (k:tk) -> IO (Maybe (tv k))
    fold : c -> (acc -> (k:tk) -> (tv k) -> IO (Bool, acc)) -> acc -> IO acc

namespace IOSet

  interface IOSet c tk | c where
    read : c -> tk -> IO Bool
    wriite : c -> tk -> IO Bool
    delete : c-> tk -> IO Bool
