||| A module defining the dependent list and its interface
module Data.DList

import Data.Singleton
import Data.DSum
import Data.Some

||| A dependent list
||| @ f  the constructor of the types of elements
||| @ ts the partameters from which the types of the lists elements are
|||      constructed
public export
data DList : (f : a -> Type) -> (ts : List a) -> Type where
  ||| The empty dependent list
  Nil : DList f Nil
  ||| Prepends a dependently typed element to a dependent list
  (::) : {0 x : a} -> f x -> DList f xs -> DList f (x :: xs)

||| Concatenate two dependent lists
public export
(++) : DList f xs -> DList f ys -> DList f (xs ++ ys)
Nil         ++ fys = fys
(fx :: fxs) ++ fys = fx :: fxs ++ fys

||| Return the length of a dependent list
export
length : DList f xs -> Nat
length Nil = Z
length (x :: xs) = S (length xs)

||| Push a component of the element type constructor to the parameter list
export
pushToParams : DList (f . g) ts -> DList f (map g ts)
-- Using `believe_me` to avoid pattern matching,
-- taking advantage from the fact that `List` and `DList` are
-- representationally equal
--
-- TODO: try implement `DList` as an alias for `HList`,
-- then you could use `id` in place of `believe_me`
pushToParams xs = believe_me xs

||| Pull a component of the element type constructor from the parameter list
export
pullFromParams : DList f (map g ts) -> DList (f . g) ts
-- Using `believe_me` to avoid pattern matching,
-- taking advantage from the fact that `List` and `DList` are
-- representationally equal
pullFromParams xs = believe_me xs

||| Generate a dependent lists from its parameters
export
replicate : (xs : List t) -> ((x : t) -> f x) -> DList f xs
replicate Nil g = Nil
replicate (x :: xs) g = g x :: replicate xs g

||| Generate a dependent lists from its parameters
export
replicate'
   : (0 f : a -> b)
  -> (xs : List a)
  -> ((x : a) -> g (f x))
  -> DList g (map f xs)
replicate' f xs gg = pushToParams (replicate xs gg)

-- TODO: rewrite in terms of `Applicative`
||| Dependent version of `traverse`.
|||
||| Map each element of a dependent list to a computation, evaluate those
||| computations and combine the results.
export
dtraverse : Monad f
        => {0 t : Type}
        -> {0 a, b : t -> Type}
        -> {0 xs : List t}

        -> ({0 x : t} -> a x -> f (b x))
        -> DList a xs
        -> f (DList b xs)

dtraverse f Nil = pure Nil
dtraverse f (ax :: axs) = do
  bx <- f ax
  bxs <- dtraverse f axs

  pure (bx :: bxs)

-- TODO: rewrite in terms of `Applicative`
||| Map each element of a list to a computation whose result type is dependent
||| on the element, evaluate those computations and combine the results.
export
dtraverse' : Monad m
        => {0 a : Type}
        -> {0 g : a -> Type}

        -> ((x : a) -> m (g x))
        -> (xs : List a)
        -> m (DList g xs)

dtraverse' f xs = dtraverse (\(Val x) => f x) (replicate xs Val)
-- This also works but I am uncomfortable with it because it creates a list of
-- "computations" (`replicate xs f`)
--dtraverse' f xs = dtraverse id (replicate xs f)


||| `foldr` version for dependent lists
export
dfoldr : ({0 x : t} -> el x -> acc -> acc) -> acc -> DList el ts -> acc
dfoldr f acc Nil = acc
dfoldr f acc (x :: xs) = f x $ dfoldr f acc xs

||| `foldl` version for dependent lists
export
dfoldl : ({0 x : t} -> acc -> el x -> acc) -> acc -> DList el ts -> acc
dfoldl f acc Nil = acc
dfoldl f acc (x :: xs) = dfoldl f (f acc x) xs

||| Apply a function to every element of a dependent list
export
dmap : ({0 x : t} -> a x -> b x) -> DList a xs -> DList b xs
dmap f Nil = Nil
dmap f (ax :: axs) = f ax :: dmap f axs

||| Turn a dependent list into a non-dependent one by applying a
||| dependency-removing function to its elements.
export
undmap : ({0 x : t} -> a x -> b) -> DList a xs -> List b
undmap f Nil = Nil
undmap f (ax :: axs) = f ax :: undmap f axs

||| The head of a dependent list
export
head : DList f (x :: xs) -> f x
head (fx :: fxs) = fx

||| The tail of a dependent list
export
tail : DList f (x :: xs) -> DList f xs
tail (fx :: fxs) = fxs

||| split a dependent list in two
export
split : {xs, xs' : List a} -> DList f (xs ++ xs') -> (DList f xs, DList f xs')
split {xs = Nil} dl = (Nil, dl)
split {xs = x :: xs''} (fx :: fxs''') = let (fxs'', fxs') = split (fxs''') in (fx :: fxs'', fxs')

||| Unzip a list with a function that returns a dependent pair
export
unzipParamsWith
   : {0 f : b -> Type}
  -> (a -> (y ** f y))
  -> List a
  -> (ys ** DList f ys)
unzipParamsWith g Nil = (Nil ** Nil)
unzipParamsWith g (x :: xs) = let
    (y ** fy) = g x
    (ys ** fys) = unzipParamsWith g xs
  in (y :: ys ** fy :: fys)

||| Unzip a list of dependent pairs
||| Returns a list of parameters and a list of the dependent elements
export
unzipParams
   : {0 f : a -> Type}
  -> (dpairs : List (x ** f x))
  -> (xs ** DList f xs)
unzipParams = unzipParamsWith id

||| Zip a dependent list with its params, according to a zipping function
export
zipParamsWith
   : {0 f : b -> Type}
  -> ((y : b) -> f y -> a)
  -> (ys ** DList f ys)
  -> List a
zipParamsWith g (Nil ** Nil) = Nil
zipParamsWith g (y :: ys ** fy :: fys) = let
    x = g y fy
    xs = zipParamsWith g (ys ** fys)
  in (x :: xs)

||| Zip a dependent list with its params
export
zipParams : {0 f : b -> Type} -> (ys ** DList f ys) -> List (y ** f y)
zipParams dpairs = zipParamsWith (\y => \fy => (y ** fy)) dpairs

||| Unzip a list of dependent sums
export
unzipDSums : List (DSum f g) -> (Some (DList f), Some (DList g))
unzipDSums Nil = (MkSome Nil, MkSome Nil)
unzipDSums ((fx :=> gx) :: dsums) = let
  (MkSome fxs, MkSome gxs) = unzipDSums dsums
  in (MkSome (fx :: fxs), MkSome (gx :: gxs))

||| Zip two dependent lists into a list of dependent sums
export
zipToDSums : DList f xs -> DList g xs -> List (DSum f g)
zipToDSums Nil Nil = Nil
zipToDSums (fx :: fxs) (gx :: gxs) = (fx :=> gx) :: zipToDSums fxs gxs

||| Zip a list of dependent pairs with an un-zipping function
export
unzipDPairsWith
   : {0 f, g, h : t -> Type}
  -> ({0 x : t} -> f x -> (g x, h x))
  -> (dpairs : List (x : t ** (f x)))
  -> (DList g (map DPair.fst dpairs), DList h (map DPair.fst dpairs))
unzipDPairsWith func Nil = (Nil, Nil)
unzipDPairsWith func ((x ** fx) :: dpairs) = let
  (gx, hx) = func fx
  (gxs, hxs) = unzipDPairsWith func dpairs
  in (gx :: gxs, hx :: hxs)

||| Zip a list of dependent pairs
||| (of pairs of elements dependent on a common parameter)
export
unzipDPairs
   : (dpairs : List (x : t ** (f x, g x)))
  -> (DList f (map DPair.fst dpairs), DList g (map DPair.fst dpairs))
unzipDPairs Nil = (Nil, Nil)
unzipDPairs ((x ** (fx, gx)) :: dpairs) = let
  (fxs, gxs) = unzipDPairs dpairs
  in (fx :: fxs, gx :: gxs)

||| Zip two dependent lists into a list of dependent pairs, according to a
||| zipping function
export
zipToDPairsWith
   : {xs : List t}
  -> {0 f, g, h : t -> Type}
  -> ({0 x : t} -> f x -> g x -> h x)
  -> DList f xs
  -> DList g xs
  -> List (x : t ** h x)
zipToDPairsWith func Nil Nil = Nil
zipToDPairsWith {xs = x :: xs} func (fx :: fxs) (gx :: gxs)
  = (x ** func fx gx) :: zipToDPairsWith func fxs gxs

||| Zip two dependent lists into a list of dependent pairs
||| (of pairs of elements dependent on a common parameter)
export
zipToDPairs
   : {xs : List t}
  -> DList f xs
  -> DList g xs
  -> List (x : t ** (f x, g x))
zipToDPairs = zipToDPairsWith (,)

||| `unzipWith` for dependent lists
dunzipWith
   : ({0 x : t} -> f x -> (g x, h x))
  -> (DList f xs)
  -> (DList g xs, DList h xs)
dunzipWith func Nil = (Nil, Nil)
dunzipWith func (fx :: fxs) = let
  (gx, hx) = func fx
  (gxs, hxs) = dunzipWith func fxs
  in (gx :: gxs, hx :: hxs)

||| `unzip` for dependent lists
dunzip
   : DList (\x => (f x, g x)) xs
  -> (DList f xs, DList g xs)
dunzip = dunzipWith id

||| `zipWith` for dependent lists
dzipWith
   : ({0 x : t} -> f x -> g x -> h x)
  -> DList f xs
  -> DList g xs
  -> DList h xs
dzipWith func Nil Nil = Nil
dzipWith func (fx :: fxs) (gx :: gxs) = (func fx gx) :: dzipWith func fxs gxs

||| `zip` for dependent lists
dzip
   : DList f xs
  -> DList g xs
  -> DList (\x => (f x, g x)) xs
dzip = dzipWith (,)

