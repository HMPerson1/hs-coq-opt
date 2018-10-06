module Simple where

import Data.Char (ord, chr)

showInt :: Integer -> String
showInt i = case compare i 0 of
              LT -> '-' : go (-i) []
              EQ -> "0"
              GT -> go i []
  where
    go :: Integer -> String -> String
    go 0 s = s
    go i s = if i < 0 then "" else
      let (tens, ones) = i `divMod` 10 in
        go tens (digit2char ones : s)

    digit2char :: Integer -> Char
    digit2char x = chr (y + ord '0')
      where
        y = fromIntegral x
