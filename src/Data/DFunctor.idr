module Data.DFunctor

||| Dependent version of `Functor`
public export
interface DFunctor (0 f : (t -> Type) -> Type) where
  ||| Analogous to `map`
  dmap : {0 a, b : t -> Type} -> ({0 x : t} -> a x -> b x) -> f a -> f b
