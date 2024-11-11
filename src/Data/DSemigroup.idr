module Data.DSemigroup

import Data.Vect

public export
interface Semigroup t => DSemigroup (0 f : t -> Type) where
  dplus : f x -> f y -> f (x <+> y)

export
implementation DSemigroup (flip Vect) where
  dplus = (++)
