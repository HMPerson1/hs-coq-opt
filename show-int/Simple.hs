module Simple where

import Data.Char (ord, chr)

showInt :: Integer -> String
showInt i = case compare i 0 of
              LT -> '-' : go (-i) []
              EQ -> "0"
              GT -> go i []
  where
    go 0 s = s
    go i s = let (tens, ones) = i `divMod` 10 in
      go tens (digit2char ones : s)

    digit2char = chr . (+ ord '0') . fromInteger
