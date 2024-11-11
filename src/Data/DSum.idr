||| A module defining a dependent sum
module Data.DSum

import Data.DOrd
import Data.DEq
import Data.Some

export infixr 1 :=>
||| A dependent sum
||| This data type is supposed to mimic the `DSum` type from Haskells "dependent-sum" package
public export
data DSum : (tag : a -> Type) -> (f : a -> Type) -> Type where
  (:=>) : {0 x : a} -> tag x -> f x -> DSum tag f

||| The first component of a dependent sum
export
fst : DSum tag f -> Some tag
fst (x :=> y) = MkSome x

||| The sencond component of a dependent sum
export
snd : DSum tag f -> Some f
snd (x :=> y) = MkSome y

||| Convert a dependent sum to `Some`
export
toSome : DSum tag f -> Some (\x => (tag x, f x))
toSome (x :=> y) = MkSome (x, y)

export
implementation (geqTag : DEq tag) => (geqf : DEq f) => Eq (DSum tag f) where
  (x :=> y) == (x' :=> y') = deq' @{geqTag} x x' && deq' @{geqf} y y'

export
implementation (geqTag : DOrd tag) => (geqf : DOrd f) => Ord (DSum tag f) where
  compare (x :=> y) (x' :=> y') = case dcompare @{geqTag} x x' of
    DLT => LT
    DGT => GT
    DEQ => dcompare' @{geqf} y y'
