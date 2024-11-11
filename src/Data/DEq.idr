||| A module defining the `DEq` interface
module Data.DEq

public export
toBool : Maybe thm -> Bool
toBool (Just _) = True
toBool Nothing = False

||| Constructors of types that allow for deciding the equality between values
||| of such types, even in the case when their types are constructed from
||| different parameters
|||
||| Modeled after the `GEq` typeclass from Haskells "some" package
public export
interface DEq (0 f : t -> Type) where
  ||| If the operands are equal, returns a proof, that their type parameters
  ||| are equal
  deq : f a -> f b -> Maybe (a = b)


||| Compare the operands and ignore the equality proof
export
deq', (==) : (impl : DEq f) => f a -> f b -> Bool
deq' fa fb = toBool (deq fa fb @{impl})
(==) = deq' @{impl}

||| Decide the inequality of the operands
export
ngeq', (/=) : (impl : DEq f) => f a -> f b -> Bool
ngeq' fa fb = not (deq' fa fb @{impl})
(/=) = ngeq' @{impl}
