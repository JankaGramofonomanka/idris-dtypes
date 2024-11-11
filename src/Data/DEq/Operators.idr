||| Module with operators for the `DEq` intrerface
||| I put them in a separate module to make it possible to avoid name
||| ambiguities.
module Data.DEq.Operators

import Data.DEq

||| Compare the operands and ignore the equality proof
||| Alias for `deq'`
export
(==) : (impl : DEq f) => f a -> f b -> Bool
(==) = deq' @{impl}

||| Decide the inequality of the operands
||| Alias for `ngeq'`
export
(/=) : (impl : DEq f) => f a -> f b -> Bool
(/=) = ngeq' @{impl}
