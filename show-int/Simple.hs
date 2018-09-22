module Simple where

import Data.Char (ord, chr)
import Numeric.Natural (Natural)

showInt :: Integer -> String
showInt i = case compare i 0 of
              LT -> '-' : go (fromInteger (-i)) []
              EQ -> "0"
              GT -> go (fromInteger i) []
  where
    go :: Natural -> String -> String
    go 0 s = s
    go i s = let (tens, ones) = i `divMod` 10 in
      go tens (digit2char ones : s)

    digit2char :: Natural -> Char
    digit2char x = chr (y + ord '0')
      where
        y = fromIntegral x
