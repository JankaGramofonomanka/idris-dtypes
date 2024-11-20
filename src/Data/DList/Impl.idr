||| Implementations of `DFunctor` and `DFoldable` for `DList`
|||
||| Separated from the `Data.DList` module, because the implementations are
||| actually for `flip DList` which makes their usefullness questionable.
module Data.DList.Impl

import public Data.DFoldable
import public Data.DFunctor
import public Data.DList

export
implementation DFunctor (flip DList xs) where
  dmap = Data.DList.dmap

export
implementation DFoldable (flip DList xs) where
  dfoldr = Data.DList.dfoldr
