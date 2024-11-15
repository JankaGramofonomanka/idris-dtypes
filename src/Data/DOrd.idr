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

export
||| Like `ordcong` but the function is implicit
ordcong'
   : {0 f : a -> b}
  -> {0 x, y : a}
  -> DOrdering x y
  -> DOrdering (f x) (f y)
ordcong' DLT = DLT
ordcong' DGT = DGT
ordcong' DEQ = DEQ

||| Takes a function and an ordering of the two values and returns an ordering
||| of the results of that function applied to these values.
|||
||| @ f   the function
||| @ x y the values
||| @ ord the ordering
export
ordcong
   : (0 f : a -> b)
  -> {0 x, y : a}
  -> (ord : DOrdering x y)
  -> DOrdering (f x) (f y)
ordcong f = ordcong' {f}

||| ``ordL `precedes` ordR`` means that, in the resulting ordering, `ordL`
||| precedes' `ordR`, that is `ordR` is considered only if `ordL` is `DEQ`
export
precedes
   : {0 a, b   : t}
  -> {0 aa, bb : tt}
  -> {0 f        : t -> tt -> ttt}
  -> (lhs      : DOrdering a        b)
  -> (rhs      : DOrdering aa       bb)
  ->             DOrdering (f a aa) (f b bb)
precedes DLT _   = DLT
precedes DGT _   = DGT
precedes DEQ DLT = DLT
precedes DEQ DGT = DGT
precedes DEQ DEQ = DEQ

||| Like `precedes`, except the preceding ordering is a regular `Ordering`
export
precedes' : Ordering -> DOrdering a b -> DOrdering a b
precedes' LT dord = DLT
precedes' EQ dord = dord
precedes' GT dord = DGT

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
|||
||| @ f the type constructor
||| @ t the parameter type
public export
interface (impl : DEq f) => DOrd (0 f : t -> Type) where
  ||| Compare the operands
  dcompare : f a -> f b -> DOrdering a b

||| Compare the operands and ignore the equality proof (if the result is `DEQ`)
export
dcompare' : (impl : DOrd f) => f a -> f b -> Ordering
dcompare' fa fb = case dcompare fa fb @{impl} of
  DLT => LT
  DEQ => EQ
  DGT => GT

||| Use only when absolutely sure that `compare x y` returns `EQ` only when `x`
||| and `y` are identical.
export
implementation [unsafeViaOrd] Ord a => POrd a where
  pcompare x y = case compare x y of
    LT => DLT
    GT => DGT
    EQ => (believe_me $ the (DOrdering x x) DEQ)

export
implementation POrd Bool where
  pcompare x y = pcompare x y @{unsafeViaOrd}

export
implementation POrd Nat where
  pcompare x y = pcompare x y @{unsafeViaOrd}

  -- A "kosher" definition:
  -- pcompare Z     Z     = DEQ
  -- pcompare (S n) (S m) = ordcong S (pcompare n m)
  -- pcompare Z     (S m) = DLT
  -- pcompare (S n) Z     = DGT

export
implementation POrd Int where
  pcompare x y = pcompare x y @{unsafeViaOrd}

export
implementation POrd Integer where
  pcompare x y = pcompare x y @{unsafeViaOrd}

export
implementation POrd Char where
  pcompare x y = pcompare x y @{unsafeViaOrd}

export
implementation POrd String where
  pcompare x y = pcompare x y @{unsafeViaOrd}

export
implementation POrd a => POrd (List a) where
  pcompare Nil Nil = DEQ
  pcompare (x :: xs) (y :: ys)
    = (pcompare x y `precedes` pcompare xs ys) {f = (::)}
  pcompare Nil (y :: ys) = DLT
  pcompare (x :: xs) Nil = DGT

export
implementation POrd a => POrd b => POrd (a, b) where
  pcompare (a1, b1) (a2, b2)
    = (pcompare a1 a2 `precedes` pcompare b1 b2) {f = (,)}
