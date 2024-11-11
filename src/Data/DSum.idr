||| A module defining a dependent sum
module Data.DSum

import Data.String

import public Data.DEq
import public Data.DOrd
import public Data.DShow
import public Data.Some

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
implementation (tagimpl : DEq tag) => (fimpl : DEq f) => Eq (DSum tag f) where
  (x :=> y) == (x' :=> y') = deq' @{tagimpl} x x' && deq' @{fimpl} y y'

export
implementation (tagimpl : DOrd tag) => (fimpl : DOrd f) => Ord (DSum tag f) where
  compare (x :=> y) (x' :=> y') = case dcompare @{tagimpl} x x' of
    DLT => LT
    DGT => GT
    DEQ => dcompare' @{fimpl} y y'

export
implementation (tagimpl : DShow tag) => (fimpl : DShow f) => Show (DSum tag f) where
  -- TODO use `showPrec` to only print parentheses when necessary
  show (x :=> y) = let
    noParens = unwords [dshow x @{tagimpl}, ":=>", dshow y @{fimpl}]
    in showParens True noParens
