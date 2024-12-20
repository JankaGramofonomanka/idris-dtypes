||| A module defining the `DEq` interface
module Data.DEq

import Data.Maybe

-------------------------------------------------------------------------------
-- (=?)
-------------------------------------------------------------------------------
export infix 1 =?
public export
(=?) : t -> t -> Type
a =? b = Maybe (a = b)

||| Takes a function and an optional proof of the equality between two values
||| and returns a proof of the equality between the results of that function
||| applied to these values
|||
||| @ f   the function
||| @ x y the values
||| @ prf the potential proof of `x = y`
export
mcong : (0 f : a -> b) -> {0 x, y : a} -> (prf : x =? y) -> f x =? f y
-- A "kosher" definition of `mcong would be this:
-- ```
-- mcong f Nothing     = Nothing
-- mcong f (Just Refl) = Just Refl
-- ```
-- but, for performance resons, I will skip the pattern matching and use
-- `believe_me` since the values are indistinguishible runtime-wise.
--
-- This should be dafinable with the `cong` function
-- (`mcong f prf = map (cong f) prf`)
-- but I cannot figure out why it doesn't type check.
mcong f prf = believe_me prf

||| Like `mcong` but the function is implicit
export
mcong' : {0 f : a -> b} -> {0 x, y : a} -> (prf : x =? y) -> f x =? f y
mcong' {f} prf = mcong f prf

||| When the condition holds, return the (optional) equality proof
||| @ meq  the (optional) equality proof
||| @ cond the condition
export
when : (cond : Bool) -> (meq : a =? b) -> a =? b
when False _  = Nothing
when True meq = meq

||| Returns the (optional) equality, but only when the condition holds
||| @ meq  the (optional) equality proof
||| @ cond the condition
export
butOnlyWhen : (meq : a =? b) -> (cond : Bool) -> a =? b
butOnlyWhen = flip when

export
and
   : {0 a, b   : t}
  -> {0 aa, bb : tt}
  -> {0 f      : t -> tt -> ttt}
  -> (lhs      : a      =? b)
  -> (rhs      : aa     =? bb)
  ->             f a aa =? f b bb
and _ Nothing = Nothing
and Nothing _ = Nothing
and (Just Refl) (Just Refl) = Just Refl

-------------------------------------------------------------------------------
-- PEq, DEq interfaces
-------------------------------------------------------------------------------
||| Similar to `Eq` but the comparison operator returns a proof that the
||| operands are equal (in the case where they are)
|||
||| The "P" in `PEq` stands for "proof"
||| Note, this is not the same as `EqP` from the "some" package from Hackage
public export
interface PEq a where
  ||| Returns a proof that the operands are equal when they are,
  ||| otherwise, returns `Nothing`
  peq : (x, y : a) -> x =? y

||| Constructors of types that allow for deciding the equality between values
||| of such types, even in the case when their types are constructed from
||| different parameters
|||
||| Modeled after the `GEq` typeclass from Haskells "some" package
|||
||| @ f the type constructor
||| @ t the parameter type
public export
interface DEq (0 f : t -> Type) where
  ||| If the operands are equal, returns a proof, that their type parameters
  ||| are equal
  deq : f a -> f b -> (a =? b)

||| Compare the operands and ignore the equality proof
export
deq' : (impl : DEq f) => f a -> f b -> Bool
deq' fa fb = isJust (deq fa fb @{impl})

||| Decide the inequality of the operands
export
ngeq' : (impl : DEq f) => f a -> f b -> Bool
ngeq' fa fb = not (deq' fa fb @{impl})

-------------------------------------------------------------------------------
-- PEq implementations
-------------------------------------------------------------------------------
||| Use only when absolutely sure that `x == y` returns `True` only when `x`
||| and `y` are identical.
export
implementation [unsafeViaEq] Eq a => PEq a where
  x `peq` y = Just (believe_me $ the (x = x) Refl) `butOnlyWhen` x == y

export
implementation PEq Bool where
  peq x y = peq x y @{unsafeViaEq}

export
implementation PEq Nat where
  peq x y = peq x y @{unsafeViaEq}

  -- A "kosher" definition:
  -- peq : (n1, n2 : Nat) -> Maybe (n1 = n2)
  -- peq Z Z = Just Refl
  -- peq (S n) (S n') = mcong S (peq n n')
  -- peq _ _ = Nothing

export
implementation PEq Int where
  peq x y = peq x y @{unsafeViaEq}

export
implementation PEq Integer where
  peq x y = peq x y @{unsafeViaEq}

export
implementation PEq Char where
  peq x y = peq x y @{unsafeViaEq}

export
implementation PEq String where
  peq x y = peq x y @{unsafeViaEq}

export
implementation PEq a => PEq (List a) where
  peq Nil Nil = Just Refl
  peq (x :: xs) (y :: ys) = (peq x y `and` peq xs ys) {f = (::)}
  peq _ _ = Nothing

export
implementation PEq a => PEq b => PEq (a, b) where
  peq (a1, b1) (a2, b2) = (peq a1 a2 `and` peq b1 b2) {f = (,)}
