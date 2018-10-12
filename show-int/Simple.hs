module Simple where

import Data.Char (ord, chr)

showInt :: Integer -> String
showInt i = case compare i 0 of
              LT -> '-' : go (-i) []
              EQ -> "0"
              GT -> go i []
  where
    go :: Integer -> String -> String
    go i s
      | i == 0    = s
      | i < 0     = error "go {< 0}"
      | otherwise = let (tens, ones) = i `divMod` 10 in
        go tens (digit2char ones : s)

    digit2char :: Integer -> Char
    digit2char x = chr (y + ord '0')
      where
        y = fromIntegral x
