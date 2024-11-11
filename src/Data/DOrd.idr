||| A module defining the `DOrd` interface
module Data.DOrd

import Data.DEq

||| An ordering of dependent types
|||
||| Modeled after the `DOrdering` type from Haskells "some" package
public export
data DOrdering : t -> t -> Type where
  DLT : DOrdering a b
  DEQ : DOrdering a a
  DGT : DOrdering a b

||| Constructors of types that allow for comparing values of such types, even
||| in the case when their types are constructed from different parameters
|||
||| Modeled after the `GCompare` typeclass from Haskells "some" package
public export
interface (impl : DEq f) => DOrd (0 f : t -> Type) where
  dcompare : f a -> f b -> DOrdering a b

export
dcompare' : (impl : DOrd f) => f a -> f b -> Ordering
dcompare' fa fb = case dcompare fa fb @{impl} of
  DLT => LT
  DEQ => EQ
  DGT => GT
