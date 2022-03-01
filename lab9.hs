-- Lab 9: Derivative-based conversion from RegExp' to FSM
-- (Brzozowski Construction)

import Data.List
import Data.Array

-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

---- Regular expressions, along with output and input
data RegExp = Empty
             | Let Char
             | Union RegExp RegExp
             | Cat RegExp RegExp
             | Star RegExp
             deriving (Show, Eq)

-- Compact display form for RegExp
newtype Compact = Compact RegExp

instance (Show Compact) where    -- use precedence to minimize parentheses
  showsPrec d (Compact r) = sp d r where
    sp d Empty         = showString "@"
    sp d (Let c)       = showString [c]
    sp d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                         sp 6 r1 .
                         showString "+" .
                         sp 6 r2
    sp d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                         sp 7 r1 .
                         sp 7 r2
    sp d (Star r1)     = sp 9 r1 .     -- prec(Star) = 8
                         showString "*"

-- Quick and dirty postfix regex parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = parse w [] where
  parse [] [r] = r
  parse ('+':xs) (r2:r1:rs) = parse xs (Union r1 r2:rs)
  parse ('.':xs) (r2:r1:rs) = parse xs (Cat r1 r2:rs)
  parse ('*':xs) (r:rs) = parse xs (Star r:rs)
  parse ('@':xs) rs = parse xs (Empty:rs)
  parse (x:xs) rs = parse xs (Let x:rs)

-- Extended regular expressions, including a name for One = Star Empty,
-- and arbitrary numbers of arguments for (associative) Union and Cat
data RegExp' = Zero | One | Let' Char |
               Union' [RegExp'] | Cat' [RegExp'] | Star' RegExp'
  deriving (Eq, Ord, Show)

-- Convert ordinary RegExps into extended RegExps
fromRE :: RegExp -> RegExp'
fromRE Empty = Zero
fromRE (Let c) = Let' c
fromRE (Union r1 r2) = Union' [fromRE r1, fromRE r2]
fromRE (Cat r1 r2) = Cat' [fromRE r1, fromRE r2]
fromRE (Star r1) = Star' (fromRE r1)

-- Convert extended RegExps into ordinary RegExps, eliminating Union' and Cat'
-- on lists of length < 2, and right-associating them on longer lists
fromRE' :: RegExp' -> RegExp
fromRE' Zero = Empty
fromRE' One = Star Empty
fromRE' (Let' c) = Let c
fromRE' (Union' []) = Empty
fromRE' (Union' [r]) = fromRE' r
fromRE' (Union' (r:rs)) = Union (fromRE' r) (fromRE' (Union' rs))
fromRE' (Cat' []) = Star Empty
fromRE' (Cat' [r]) = fromRE' r
fromRE' (Cat' (r:rs)) = Cat (fromRE' r) (fromRE' (Cat' rs))
fromRE' (Star' r) = Star (fromRE' r)

-- Basic postfix parser for RE', assuming binary + and ., including 0 and 1
toRE' :: String -> RegExp'
toRE' w = parse w [] where
  parse [] [r] = r
  parse ('0':xs) rs = parse xs (Zero:rs)
  parse ('1':xs) rs = parse xs (One:rs)
  parse ('+':xs) (r2:r1:rs) = parse xs (Union' [r1,r2]:rs)
  parse ('.':xs) (r2:r1:rs) = parse xs (Cat' [r1,r2]:rs)
  parse ('*':xs) (r:rs) = parse xs (Star' r:rs)
  parse (x:xs) rs = parse xs (Let' x:rs)


-- An extended regular expression simplifier
simp :: RegExp' -> RegExp'
simp Zero = Zero
simp One = One
simp (Let' c) = Let' c
simp (Union' rs) = union' $ flat_uni $ map simp rs
simp (Cat' rs) = union' $ flat_cat $ map simp rs
simp (Star' r) = star' $ simp r

-- Smart constructor for Union' that normalizes its arguments and
-- handles the empty and singleton cases
union' :: [RegExp'] -> RegExp'
union' rs =  case norm rs of
  []  ->  Zero
  [r] -> r
  rs  -> Union' rs

-- Smart constructor for Cat' that handles the empty and singleton cases
cat' :: [RegExp'] -> RegExp'
cat' [] = One
cat' [r] = r
cat' rs = Cat' rs

-- Smart constructor for Star' that handles the constant and Star' cases
star' :: RegExp' -> RegExp'
star' Zero = One
star' One = One
star' (Star' r) = star' r
star' r = Star' r

-- Flatten a list of arguments to Union'; assumes each argument is simplified
flat_uni :: [RegExp'] -> [RegExp']
flat_uni [] = []
flat_uni (Zero:rs) = flat_uni rs
flat_uni (Union' rs':rs) = rs' ++ flat_uni rs
flat_uni (r:rs) = r : flat_uni rs

-- Flatten a list of arguments to Cat', turning them into a list of arguments
-- to Union'; assumes each argument is simplified
flat_cat :: [RegExp'] -> [RegExp']
flat_cat rs = fc [] rs where
  -- fc (args already processed, in reverse order) (args still to be processed)
  fc :: [RegExp'] -> [RegExp'] -> [RegExp']
  fc pr [] = [cat' $ reverse pr]
  fc pr (Zero:rs) = []
  fc pr (One:rs) = fc pr rs
  fc pr (Cat' rs':rs) = fc (reverse rs' ++ pr) rs
  fc pr (Union' rs':rs) = concat $ map (fc pr . (:rs)) rs'
  fc pr (r:rs) = fc (r:pr) rs


-- Finite state machines, now indexed by the type of their states
-- M = (states, start, finals, transitions)  
type FSM a = ([a], a, [a], a -> Char -> a)


-- Change the states of an FSM from an equality type to Int 
-- and use an array lookup for the transition function
intify :: Eq a => FSM a -> FSM Int
intify (qs, s, fs, d) = ([0..n-1], s', fs', d') where
  n = length qs
  m = length sigma
  s'  = ind qs s
  fs' = map (ind qs) fs
  arr = listArray ((0,0), (n-1,m-1)) [ind qs (d q a) | q <- qs, a <- sigma]
  d' q a = arr ! (q, ind sigma a)
  ind (q':qs) q = if q == q' then 0 else 1 + ind qs q

-- Unary set closure (where "set" = normalized list)
-- uclosure xs g == smallest set containing xs and closed under g
uclosure :: Ord a => [a] -> (a -> [a]) -> [a]
uclosure xs g = sort $ stable $ iterate close (xs, []) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') $ concatMap g fr


---------------- Lab 9 begins here ----------------
{-
byp :: RegExp -> Bool
byp Empty=False
byp (Let x)=False
byp (Star x)=True
byp (Union x y)=byp x || byp y
byp (Cat x y)=byp x && byp y
-}
-- Bypassable for extended REs, computed directly by recursion.
byp :: RegExp' -> Bool
byp Zero = False
byp One = True
byp (Let' c)=False
byp (Star' re)=True
byp (Union' re)= or[byp x | x <- re]
byp (Cat' re)= and [ byp x | x <- re]

-- Regular-expression derivatives (aka left quotients) on extended REs,
-- computed directly by recursion.
deriv :: Char -> RegExp' -> RegExp'
deriv a Zero = Zero
deriv a One = Zero
deriv a (Let' c)= if c==a then One else Zero
deriv a (Union' re)= uhp a re where
  uhp a [] = Zero
  uhp a re = simp (Union' [ deriv a x| x <- re])
deriv a (Cat' re)= chp a re where
  chp a [] =Zero
  chp a (x:xs)=if not( byp x) then simp (Cat' (deriv a x:xs)) else simp (Union' [Cat' (deriv a x:xs), deriv a (Cat' xs)])
deriv a (Star' re) = simp(Cat' [deriv a re, Star' re])

-- Convert an RegExp' to an FSM using the derivative (Brzozowski) construction.
-- States are SIMPLIFIED extended REs.  Note: to construct all the states,
-- you will have to use another closure process.
--([a], a, [a], a -> Char -> a)
conv :: RegExp' -> FSM RegExp'
conv r = (qs,s,[ simp re | re <-qs, byp re ],der) where
  s = simp r
  der re a = deriv a re
  qs = uclosure [s] transf where
    transf re = [der re a | a <- sigma]
      


-- Test, and show your tests! You may copy code from previous labs to help.

strings :: Int -> [String]
strings n = concat [strs i | i <- [0..n]] where
  strs 0 = [""]
  strs n = [a:xs | a <- sigma, xs <- strs (n-1)]

accept2 :: Eq a=>FSM a-> [Char] -> Bool
accept2 (qs, s, fs, d)  = aux s  where
-- aux q w = whether the machine, starting in q, accepts w (recursive in w)
  aux q [] = q `elem` fs
  aux q (x:xs)= accept2 (qs,d q x,fs,d) xs

match2 :: RegExp' -> String -> Bool
match2 r w = m [fromRE' r] False w where
  m :: [RegExp] ->Bool->String->Bool
  m [] c w=not c && null w
  m [Empty] c w= not c && null w 
  m (Let x:rs) c w= not(null w) && x==head w && m rs False (tail w)
  m ((Union r1 r2):rs) c w= m (r1:rs) c w || m (r2:rs) c w
  m ((Cat r1 r2):rs) c w= m (r1:r2:rs) c w || c && byp (fromRE r1) && m (r2:rs) True w
  m (Star r1:rs) c w= (not c && m rs c w) || m (r1:Star r1:rs) True w

-- This test function will return a list of all strings that from sigma and accepted by the machine
test :: RegExp' -> [String]
test r =  [w| w <- strings 10,match2 r w,accept2 m w] where m = conv r

{-
  test (Cat'[Let' 'a', Let' 'b'])=["ab"]
  
  test (Union'[Let' 'a', Let' 'b'])=["a","b"]

  test (Union'[Cat' [Let' 'a', Let' 'b'], Let' 'b'])= ["b","ab"]

  test (Star'(Cat'[Let' 'a', Let' 'b']))= ["","ab","abab","ababab","abababab","ababababab"]
-}