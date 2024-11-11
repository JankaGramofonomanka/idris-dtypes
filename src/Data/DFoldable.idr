module Data.DFoldable

||| Dependent version of `Foldable`
||| A minimal implementation includes `dfoldr`
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
dfoldl
   : (impl : DFoldable f)
  => {0 el : t -> Type}
  -> ({0 x : t} -> acc -> el x -> acc)
  -> acc
  -> f el
  -> acc
dfoldl f z tr = dfoldr f' z tr @{impl} where
  f' : {0 x : t} -> el x -> acc -> acc
  f' el acc = f acc el

-- separated from the interface definition due to weird errors
-- (the errors occur in modules importing this one)
export
dnull : DFoldable f => f el -> Bool
dnull xs = dfoldr {f} {acc = Lazy Bool} (\ _,_ => False) True xs

-- separated from the interface definition due to weird errors
||| `DFoldable` version of `foldlM`
export
dfoldlM
   : {0 m : Type -> Type}
  -> {0 el : t -> Type}
  -> DFoldable f
  => Monad m
  => (funcM : {0 x : t} -> acc -> el x -> m acc)
  -> (init : acc)
  -> (input : f el)
  -> m acc
dfoldlM fm a0 = dfoldl {f} {el} (\ma, b => ma >>= flip fm b) (pure a0)

-- separated from the interface definition due to weird errors
||| `DFoldable` version of `foldMap`
export
dfoldMap : (impl : DFoldable f) => Monoid m => ({0 x : t} -> a x -> m) -> f a -> m
dfoldMap f = dfoldr ((<+>) . f) neutral @{impl}
