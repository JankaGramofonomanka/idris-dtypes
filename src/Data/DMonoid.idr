module Data.DMonoid

import Data.Vect
import Data.DSemigroup

export
interface Monoid t => DSemigroup f => DMonoid (0 f : t -> Type) where
  dneutral : f neutral

export
implementation DSemigroup (flip Vect) where
  dneutral = Nil
