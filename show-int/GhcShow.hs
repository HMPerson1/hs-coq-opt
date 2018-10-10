{-# LANGUAGE CPP, UnboxedTuples #-}

module GhcShow where

import GHC.Base (unsafeChr, ord, quotRemInt)
--import GHC.Num (quotRemInteger)
quotRemInteger :: Integer -> Integer -> (# Integer, Integer #)
quotRemInteger a b = let (q,r) = divMod a b in (# q, r #)

showInt :: Integer -> String
showInt i = integerToString i ""

-- copied from GHC/libraries/base/GHC/Show.hs
-- unpacking C# removed

-- these are supposed to be platform-dependent
#define DIGITS       18
#define BASE         1000000000000000000

-- Divide and conquer implementation of string conversion
integerToString :: Integer -> String -> String
integerToString n0 cs0
    | n0 < 0    = '-' : integerToString' (- n0) cs0
    | otherwise = integerToString' n0 cs0
    where
    integerToString' :: Integer -> String -> String
    integerToString' n cs
        | n < BASE  = jhead (fromInteger n) cs
        | otherwise = jprinth (jsplitf (BASE*BASE) n) cs

    -- Split n into digits in base p. We first split n into digits
    -- in base p*p and then split each of these digits into two.
    -- Note that the first 'digit' modulo p*p may have a leading zero
    -- in base p that we need to drop - this is what jsplith takes care of.
    -- jsplitb the handles the remaining digits.
    jsplitf :: Integer -> Integer -> [Integer]
    jsplitf p n
        | p <= 1    = errorWithoutStackTrace "jsplitf {<= 1}"
        | p > n     = [n]
        | otherwise = jsplith p (jsplitf (p*p) n)

    jsplith :: Integer -> [Integer] -> [Integer]
    jsplith p (n:ns) =
        case n `quotRemInteger` p of
        (# q, r #) ->
            if q > 0 then q : r : jsplitb p ns
                     else     r : jsplitb p ns
    jsplith _ [] = errorWithoutStackTrace "jsplith: []"

    jsplitb :: Integer -> [Integer] -> [Integer]
    jsplitb _ []     = []
    jsplitb p (n:ns) = case n `quotRemInteger` p of
                       (# q, r #) ->
                           q : r : jsplitb p ns

    -- Convert a number that has been split into digits in base BASE^2
    -- this includes a last splitting step and then conversion of digits
    -- that all fit into a machine word.
    jprinth :: [Integer] -> String -> String
    jprinth (n:ns) cs =
        case n `quotRemInteger` BASE of
        (# q', r' #) ->
            let q = fromInteger q'
                r = fromInteger r'
            in if q > 0 then jhead q $ jblock r $ jprintb ns cs
                        else jhead r $ jprintb ns cs
    jprinth [] _ = errorWithoutStackTrace "jprinth []"

    jprintb :: [Integer] -> String -> String
    jprintb []     cs = cs
    jprintb (n:ns) cs = case n `quotRemInteger` BASE of
                        (# q', r' #) ->
                            let q = fromInteger q'
                                r = fromInteger r'
                            in jblock q $ jblock r $ jprintb ns cs

    -- Convert an integer that fits into a machine word. Again, we have two
    -- functions, one that drops leading zeros (jhead) and one that doesn't
    -- (jblock)
    jhead :: Int -> String -> String
    jhead n cs
        | n < 10    = case unsafeChr (ord '0' + n) of
            c -> c : cs
        | otherwise = case unsafeChr (ord '0' + r) of
            c -> jhead q (c : cs)
        where
        (q, r) = n `quotRemInt` 10

    jblock = jblock' {- ' -} DIGITS

    jblock' :: Int -> Int -> String -> String
    jblock' d n cs
        | d == 1    = case unsafeChr (ord '0' + n) of
             c -> c : cs
        | d < 1     = errorWithoutStackTrace "jblock' {< 1}"
        | otherwise = case unsafeChr (ord '0' + r) of
             c -> jblock' (d - 1) q (c : cs)
        where
        (q, r) = n `quotRemInt` 10
