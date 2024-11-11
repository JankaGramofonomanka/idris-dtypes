module Data.DFoldable

||| Dependent version of `Foldable`
public export
interface DFoldable (0 f : (t -> Type) -> Type) where
  -- TODO what about dependent accumulator?
  ||| Dependent version of `foldr`
  dfoldr
     : {0 el : t -> Type}
    -> ({0 x : t} -> el x -> acc -> acc)
    -> acc
    -> f el
    -> acc

  -- there seems to be a bug, this does not type-check. If you put the
  -- definition of `dfoldl` before `dfoldr`, then `dfoldr` does not type-check
  -- thus a default implementation of `dfoldl` is moved outside the interface
  -- definition
  --||| Dependent version of `foldl`
  --dfoldl
  --   : (impl : DFoldable f)
  --  => {0 el : t -> Type}
  --  -> ({0 x : t} -> acc -> el x -> acc)
  --  -> acc
  --  -> f el
  --  -> acc
  --dfoldl f z tr = dfoldr f' z tr @{impl} where
  --  f' : {0 x : t} -> el x -> acc -> acc
  --  f' el acc = f acc el

||| Default implementation of `dfoldl`
||| Separated from the interface definition due to what seems to be a compiler
||| bug.
public export
defaultDfoldl
   : (impl : DFoldable f)
  => {0 el : t -> Type}
  -> ({0 x : t} -> acc -> el x -> acc)
  -> acc
  -> f el
  -> acc
defaultDfoldl f z tr = dfoldr f' z tr @{impl} where
  f' : {0 x : t} -> el x -> acc -> acc
  f' el acc = f acc el
