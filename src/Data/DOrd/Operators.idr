||| Module with operators for the `DOrd` intrerface
||| I put them in a separate module to make it possible to avoid name
||| ambiguities.
module Data.DOrd.Operators

import Data.DOrd

export
(<) : (impl : DOrd f) => f a -> f b -> Bool
fa < fb = dcompare' fa fb @{impl} == LT

export
(>) : (impl : DOrd f) => f a -> f b -> Bool
fa > fb = dcompare' fa fb @{impl} == GT

export
(<=) : (impl : DOrd f) => f a -> f b -> Bool
fa <= fb = dcompare' fa fb @{impl} `elem` [LT, EQ]

export
(>=) : (impl : DOrd f) => f a -> f b -> Bool
fa >= fb = dcompare' fa fb @{impl} `elem` [GT, EQ]
