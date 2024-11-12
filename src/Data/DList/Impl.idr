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
