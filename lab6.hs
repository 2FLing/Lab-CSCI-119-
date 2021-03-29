-- Lab 6:  FSM constructions for regular operators

import Data.List
import Data.Array


-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"
-- Recursive reimplementation of strings function from Lab 4
strings :: Int -> [String]
strings n = concat [strs i | i <- [0..n]] where
  strs 0 = [""]
  strs n = [a:xs | a <- sigma, xs <- strs (n-1)]

-- Finite state machines, now indexed by the type of their states
-- M = (states, start, finals, transitions)  
type FSM a = ([a], a, [a], a -> Char -> a)


---------------- Your solution to Lab 5, ported to FSM a -------------------

-- Note: in most cases, you will need to add an Eq a => constraint

unique :: Eq a => [a] -> Bool
unique []=True
unique (x:xs)= notElem x xs && unique xs

subset :: (Foldable t, Eq a) => [a] -> t a -> Bool
subset xs ys= and [ x `elem` ys | x <- xs]

trasnsition :: Eq a => (a -> Char -> a) -> [a] -> Bool
trasnsition d qs= and [d q c `elem` qs | q <- qs, c <- sigma]

checkFSM :: Eq a =>FSM a-> Bool
checkFSM (qs, s, fs, d) = unique qs &&  elem s qs && subset fs qs && trasnsition d qs

-- Gives the delta* function (recursive in w)
dstar :: FSM a-> a-> [Char] -> a
dstar m q w = dh m q w where
  dh (qs, s, fs, d) q []= q
  dh (qs, s, fs, d) q (a:rw) = dh m (d q a) rw

-- Machine acceptance, Definition 1 (via delta*)
accept1 :: Eq a => FSM a-> [Char] -> Bool
accept1 m w = ah m w where
  ah (qs, s, fs, d) w = dstar m s w `elem` fs

accept2 :: Eq a=>FSM a-> [Char] -> Bool
accept2 (qs, s, fs, d)  = aux s  where
-- aux q w = whether the machine, starting in q, accepts w (recursive in w)
  aux q [] = q `elem` fs
  aux q (x:xs)= accept2 (qs,d q x,fs,d) xs

---------------- Some additional useful functions --------------------------

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Cartesian product (preserves normalization)
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- Powerset  (preserves normalization)
power :: [a] -> [[a]]
power [] = [[]]
power (x:xs) = let ys = power xs
               in [] : map (x:) ys ++ tail ys

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys


---------------- Lab 6 begins here -----------------------------------------

-- Complete the FSM constructions for the regular expression operators
-- and test your functions adquately

-- (qs, s, fs, d)
-- Machine that accepts the empty language
emptyFSM :: FSM Int
emptyFSM = ([0],0,[0],d) where
  d q c= q 


-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM Int
letterFSM a = ([0,1,2],0,[1],d) where
  d 0 c= if c ==a then 1 else 2
  d 1 c=2
  d 2 c=2

-- Machine that accepts the union of the languages accepted by m1 and m2
unionFSM :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a, b)
unionFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1,s2)
  fs = [(a,b)| a<- fs1, b <- qs2]++[(a,b) | a <- qs1, b <- fs2]
  d = dh where
    dh (x,y) c =(d1 x c,d2 y c)
-- Machine that accepts the concatenation of the languages accepted by m1 and m2
catFSM :: (Eq a, Ord b) => FSM a -> FSM b -> FSM (a, [b])
catFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< power qs2
  s  = (s1,adj s1) where
    adj s1= [s2 | s1 `elem` fs1]
  fs = [x | x <- qs, overlap (snd x) fs2]
  d  = dc where
    dc (q,x) a=(d1 q a, norm [d2 b a | b <- adj q x]) where
      adj q x= if q `elem` fs1 then x++[s2] else x

-- Machine that accepts the Kleene star of the language accepted by m1
starFSM :: Ord a => FSM a -> FSM [a]
starFSM (qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = power qs1
  s  = []
  fs = [] : [x | x <- qs, overlap x fs1]
  d  =  dc where
    dc x a = norm $ correct (if null x then [d1 s1 a] else [d1 y a | y <- x]) where
      correct x= if overlap x fs1 then x++[s1] else x



---------------- Bonus Features (for testing and experimenting) ------------

-- Unary set closure (where "set" = normalized list)
-- uclosure xs g == smallest set containing xs and closed under g
uclosure :: Ord a => [a] -> (a -> [a]) -> [a]
uclosure xs g = sort $ stable $ iterate close (xs, []) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') $ concatMap g fr

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable m@(qs, s, fs, d) = (qs', s, fs', d) where
  qs' = uclosure [s] (\q -> map (d q) sigma)
  fs' = filter (`elem` fs) qs'

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

reduce :: Ord a => FSM a -> FSM Int
reduce = intify . reachable

---- Regular expressions, along with input and output
data RegExp = Empty                -- Empty language
            | Let Char             -- Single letter language
            | Union RegExp RegExp  -- Union
            | Cat RegExp RegExp    -- Concatenation
            | Star RegExp          -- Kleene star
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

-- Quick and dirty postfix RegExp parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = go w [] where
  go [] [r]              = r
  go ('+':xs) (r2:r1:rs) = go xs (Union r1 r2:rs)
  go ('.':xs) (r2:r1:rs) = go xs (Cat r1 r2:rs)
  go ('*':xs) (r:rs)     = go xs (Star r:rs)
  go ('0':xs) rs         = go xs (Empty:rs)
  go ('1':xs) rs         = go xs (Star Empty:rs)
  go (x:xs) rs           = go xs (Let x:rs)

-- Use constructions above to get reduced machine associated with regex
-- Warning: it can take a lot of time/memory to compute these for "big" regex's
-- We will see much better ways later in the course
re2fsm :: RegExp -> FSM Int
re2fsm Empty = emptyFSM
re2fsm (Let c) = letterFSM c
re2fsm (Union r1 r2) = reduce $ unionFSM (re2fsm r1) (re2fsm r2)
re2fsm (Cat r1 r2) = reduce $ catFSM (re2fsm r1) (re2fsm r2)
re2fsm (Star r1) = reduce $ starFSM (re2fsm r1)
