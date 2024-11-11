||| A module defining a dependent sum
module Data.DSum

import Data.GCompare
import Data.GEq
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
implementation (geqTag : GEq tag) => (geqf : GEq f) => Eq (DSum tag f) where
  (x :=> y) == (x' :=> y') = geq' @{geqTag} x x' && geq' @{geqf} y y'

export
implementation (geqTag : GCompare tag) => (geqf : GCompare f) => Ord (DSum tag f) where
  compare (x :=> y) (x' :=> y') = case gcompare @{geqTag} x x' of
    GLT => LT
    GGT => GT
    GEQ => gcompare' @{geqf} y y'
