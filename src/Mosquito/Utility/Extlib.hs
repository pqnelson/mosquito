-- |A module containing some useful combinators missing from the Haskell
--  standard library.
module Mosquito.Utility.Extlib (
  fst3, snd3, thd3
) where

  -- |Returns the first component of a triple.
  fst3 :: (a, b, c) -> a
  fst3 (x, _, _) = x

  -- |Returns the second component of a triple.
  snd3 :: (a, b, c) -> b
  snd3 (_, y, _) = y

  -- |Returns the third component of a triple.
  thd3 :: (a, b, c) -> c
  thd3 (_, _, z) = z