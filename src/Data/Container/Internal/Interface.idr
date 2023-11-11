module Data.Container.Internal.Interface


%default total

-- --------------------------------------------------------------------------

namespace IODContainer

  interface IODContainer c tk tv | c where
    read : HasIO io => c -> (k:tk) -> io (Maybe (tv k))
    write : HasIO io => c -> (k:tk) -> (tv k) -> io (Maybe (tv k))
    update : HasIO io => c -> (k:tk) -> (tv k) -> io (Maybe (tv k))
    delete : HasIO io => c -> (k:tk) -> io (Maybe (tv k))
    fold : HasIO io => c -> (acc -> (k:tk) -> (tv k) -> io (Bool, acc)) -> acc -> io acc
    
namespace IOSet

  interface IOSet c tk | c where
    read : HasIO io => c -> tk -> io Bool
    wriite : HasIO io => c -> tk -> io Bool
    delete : HasIO io => c-> tk -> io Bool


