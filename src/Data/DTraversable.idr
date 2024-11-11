module Data.DTraversable

import Data.DFunctor
import Data.DFoldable

||| Dependent version of `Traversable`
public export
interface {-(DFunctor tr, DFoldable tr) =>-} DTraversable (0 tr : {0 t : Type} -> (t -> Type) -> Type) where
  ||| Dependent version of `traverse`
  dtraverse
     : Applicative f
    => {0 t : Type}
    -> {0 a, b : t -> Type}

    -> ({0 x : t} -> a x -> f (b x))
    -> tr a
    -> f (tr b)
