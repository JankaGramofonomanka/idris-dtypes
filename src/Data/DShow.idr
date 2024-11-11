module Data.DShow

public export
ShowS : Type
ShowS = String -> String

||| Dependent version of `Show`
||| Inspired by the `GShow` typeclass from Haskells "some" package
||| Modeled after the `Show` interface from `base`
public export
interface DShow (0 f : t -> Type) where
  dshow : f a -> String
  dshow x = dshowPrec {f} Open x

  dshowPrec : Prec -> f a -> String
  dshowPrec _ x = dshow {f} x

export
dshowArg : (impl : DShow f) => f x -> String
dshowArg x = " " ++ dshowPrec App x @{impl}
