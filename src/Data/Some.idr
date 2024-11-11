||| A module defining the `Some` type
module Data.Some

import Data.DEq
import Data.DOrd
import Data.DShow

||| Wraps a dependent type, so that its parameter is hidden.
||| Values of dependent types, wrapped this way, have the same type
||| @ f the type constructor of types of the wrapped values.
public export
data Some : (f : t -> Type) -> Type where
  ||| Hide the type parameter of the type of a value
  ||| @ a the parameter of the type of the wrapped value
  ||| @ x the wrapped value
  MkSome : {0 a : t} -> (x : f a) -> Some f

export
implementation (impl : DEq f) => Eq (Some f) where
  MkSome x == MkSome y = deq' x y @{impl}

export
implementation (impl : DOrd f) => Ord (Some f) where
  compare (MkSome x) (MkSome y) = case dcompare x y @{impl} of
    DLT => LT
    DGT => GT
    DEQ => EQ

export
implementation (impl : DShow f) => Show (Some f) where
  showPrec prec (MkSome fx) = showCon prec "MkSome" (dshowArg fx @{impl})

||| Apply a dependency-removing function to the value wrapped in `Some` and
||| drop the wrapper
export
withSome : Some f -> ({0 x : a} -> f x -> b) -> b
withSome (MkSome thing) some = some thing

||| Apply a function to the wrapped value
export
map : ({0 a : t} -> f a -> g a) -> Some f -> Some g
map f (MkSome x) = MkSome (f x)
