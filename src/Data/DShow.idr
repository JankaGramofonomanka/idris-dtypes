module Data.DShow

||| Equivalent of `Show` for single-parameter dependent types
|||
||| Inspired by the `GShow` typeclass from Haskells "some" package.
||| Modeled after the `Show` interface from `base`.
public export
interface DShow (0 f : t -> Type) where

  ||| Analogous to `show`
  dshow : f a -> String
  dshow x = dshowPrec {f} Open x

  ||| Analogous to `showPrec`
  dshowPrec : Prec -> f a -> String
  dshowPrec _ x = dshow {f} x

||| `Prelude.Show.showArg` in terms of `DShow`
export
dshowArg : (impl : DShow f) => f x -> String
dshowArg x = " " ++ dshowPrec App x @{impl}
