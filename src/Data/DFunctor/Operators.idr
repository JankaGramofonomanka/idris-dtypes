||| Module with operators for the `DFunctor` intrerface
||| I put them in a separate module to make it possible to avoid name
||| ambiguities.
module Data.DFunctor.Operators

import Data.DFunctor

||| An infix alias for `dmap`
public export
(<$>) : DFunctor f => {0 a, b : t -> Type} -> ({0 x : t} -> a x -> b x) -> f a -> f b
(<$>) func x = dmap {f} func x

||| Flipped version of `<$>`, an infix alias for `dmap`
public export
(<&>) : DFunctor f => {0 a, b : t -> Type} -> f a -> ({0 x : t} -> a x -> b x) -> f b
(<&>) x func = dmap {f} func x
