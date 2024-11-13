||| A module defining the `DOrd` interface
module Data.DOrd

import public Data.DEq

||| An ordering of single-parameter dependent types
|||
||| Modeled after the `GOrdering` type from Haskells "some" package
public export
data DOrdering : t -> t -> Type where
  DLT : DOrdering a b
  DEQ : DOrdering a a
  DGT : DOrdering a b

||| Similar to `Ord` but the operands can be equal only when they actually are,
||| that is, when the statement `p = q` is true (there is a `Refl : (p = q)`),
||| where `p` and `q` are the operands
|||
||| The "P" in `POrd` stands for "proof"
||| Note, this is not the same as `OrdP` from the "some" package from Hackage
public export
interface POrd a where
  ||| Compare two values
  pcompare : (x, y : a) -> DOrdering x y

||| Constructors of types that allow for comparing values of such types, even
||| in the case when their types are constructed from different parameters
|||
||| Modeled after the `GCompare` typeclass from Haskells "some" package
public export
interface (impl : DEq f) => DOrd (0 f : t -> Type) where
  dcompare : f a -> f b -> DOrdering a b

export
dcompare' : (impl : DOrd f) => f a -> f b -> Ordering
dcompare' fa fb = case dcompare fa fb @{impl} of
  DLT => LT
  DEQ => EQ
  DGT => GT

||| Use only when absolutely sure that `compare x y` returns `EQ` only when `x`
||| and `y` are identical.
export
implementation [unsafeViaEq] Ord a => POrd a where
  pcompare x y = case compare x y of
    LT => DLT
    GT => DGT
    EQ => (believe_me $ the (DOrdering x x) DEQ)

export
implementation POrd Bool where
  pcompare x y = pcompare x y @{unsafeViaEq}

export
implementation POrd Nat where
  pcompare x y = pcompare x y @{unsafeViaEq}

  -- A "kosher" definition:
  -- pcompare Z Z = DEQ
  -- pcompare (S n) (S m) = case pcompare n m of
  --     DLT => DLT
  --     DGT => DGT
  --     DEQ => DEQ
  -- pcompare Z (S m) = DLT
  -- pcompare (S n) Z = DGT

export
implementation POrd Int where
  pcompare x y = pcompare x y @{unsafeViaEq}

export
implementation POrd Integer where
  pcompare x y = pcompare x y @{unsafeViaEq}

export
implementation POrd Char where
  pcompare x y = pcompare x y @{unsafeViaEq}

export
implementation POrd String where
  pcompare x y = pcompare x y @{unsafeViaEq}

export
implementation POrd a => POrd (List a) where
  pcompare Nil Nil = DEQ
  pcompare (x :: xs) (y :: ys) = case pcompare x y of
    DLT => DLT
    DGT => DGT
    -- TODO write an analogy to `mcong`
    DEQ => case pcompare xs ys of
      DLT => DLT
      DGT => DGT
      DEQ => DEQ
  pcompare Nil (y :: ys) = DLT
  pcompare (x :: xs) Nil = DGT

export
implementation POrd a => POrd b => POrd (a, b) where
  pcompare (a1, b1) (a2, b2) = case pcompare a1 a2 of
    DLT => DLT
    DGT => DGT
    -- TODO write an analogy to `mcong`
    DEQ => case pcompare b1 b2 of
      DLT => DLT
      DGT => DGT
      DEQ => DEQ
