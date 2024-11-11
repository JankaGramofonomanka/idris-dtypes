module Data.DFunctor

public export
interface DFunctor (0 f : (t -> Type) -> Type) where
  dmap : {a, b : t -> Type} -> ({0 x : t} -> a x -> b x) -> f a -> f b
