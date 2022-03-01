-- Lab 8: Additional constructions, nondeterministic machines

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


---------------- Given functions ----------------

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

-- delta* construction
star :: (a -> Char -> a) -> (a -> [Char] -> a)
star = foldl'

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
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Let x:rs)


---------------- Part 1: Additional constructions ----------------
-- Define the operations given in Section 7 of the notes
-- Intersection
inters :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a,b)
inters a b = ih a b where
  ih (q1,s1,fs1,d1) (q2,s2,fs2,d2)=(q1 >< q2,(s1,s2),fs1 >< fs2, d) where
    d (x1,x2) a = (d1 x1 a , d2 x2 a)

-- Symmetric difference (xor)
symdiff :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a,b)
symdiff a b = sh a b where
  sh (q1,s1,fs1,d1) (q2,s2,fs2,d2)= (q1 >< q2, (s1,s2),([(a,b)| a<- fs1, b <- q2]++[(a,b) | a <- q1, b <- fs2])\\(fs1 >< fs2),d) where
    d (x1,x2) a = (d1 x1 a , d2 x2 a)
    
-- Complement
compl :: Eq a => FSM a -> FSM a
compl (q,s,f,d)=(q,s,q\\f,d) 

-- Direct homomorphic image: k is a substitution
onestr :: String -> RegExp
onestr []= Empty
onestr [x]= Let x
onestr (x:xs) =  Cat (Let x) (onestr xs)

homo_dir :: (Char -> String) -> RegExp -> RegExp
homo_dir k re= hd k re where
  hd k Empty=Empty
  hd k (Let c) = onestr (k c)
  hd k (Cat a b)=Cat (hd k a) (hd k b)
  hd k (Union a b)= Union (hd k a) (hd k b)
  hd k (Star a)= Star (hd k a)
-- Inverse homomorphic image
homo_inv :: Eq a => (Char -> String) -> FSM a -> FSM a
homo_inv k (q, s, f, d1)= (q,s,f, d2) where
  d2 q a = ds q (k a) where
    ds q [] =q
    ds q (a:w) = ds (d1 q a) w 

-- Right quotient by a finite language
quot_right :: Eq a => [String] -> FSM a -> FSM a
quot_right strl (qs,s,f,d) = (qs, s, f1,d) where
  f1= [q |q <- qs, w <- strl, (ds q w) `elem` f] where
    ds q []=q
    ds q (a:w)= ds (d q a) w

---------------- Part 2: Nondeterministic machines ----------------

-- Nondeterministic FSMs, indexed by their type of state
-- All states are normalized and the output of d is normalized
-- M = (states, starts, finals, transitions)  
type Trans a = a -> Char -> [a]
type NFSM a = ([a], [a], [a], Trans a)

-- nap_hat d qs a == normalized list of all transitions possible from qs on a
nap_hat :: Ord a => Trans a -> [a] -> Char -> [a]
nap_hat d qs a= norm [q | q <- qs, x <- qs , q <- d x a]
-- nap_hat_star d qs w == normalized list of transitions possible from qs on w
nap_hat_star :: Ord a => Trans a -> [a] -> [Char] -> [a]
nap_hat_star d qs []= qs
nap_hat_star d qs (a:w)= nap_hat_star d (nap_hat d qs a) w 

-- nacc m w == m accepd the string w
nacc :: Ord a => NFSM a -> [Char] -> Bool
nacc (_,s,f,d) w = overlap (nap_hat_star d s w) f  


-- Nondeterministic FSMs with epsilon moves, indexed by their type of state
-- M = (states, starts, finals, transitions, epsilon-moves)
type Eps a = [(a, a)]
type EFSM a = ([a], [a], [a], Trans a, Eps a)

-- Normalized epsilon closure of a set of states (Hint: use uclosure)
eclose :: Ord a => Eps a -> [a] -> [a]
eclose eps q= uclosure q d where
  d a = norm [ snd x | x <- eps, fst x== a]
-- eap_has d es qs a == eclosure of transitions possible from qs on a
eap_hat :: Ord a => (Trans a, Eps a) -> [a] -> Char -> [a]
eap_hat (d,eps) qs a = eclose eps (norm $ fs qs a) where
  fs [] a = []
  fs (x:xs) a = d x a ++ fs xs a

eacc :: Ord a => EFSM a -> [Char] -> Bool
eacc (_,s,fs,_,_)[] = and [ x `elem` fs | x <- s]
eacc (_,s,fs,tran,eps) (a:w)= overlap (shat (eclose eps s) (a:w)) fs where
  shat q [] = q
  shat q (a:w) = shat (eap_hat (tran,eps) q a)  w



---------------- Part 3: Conversion between machines ----------------

-- Easy conversion from FSM to NFSM (given)
fsm_to_nfsm :: Eq a => FSM a -> NFSM a
fsm_to_nfsm (q,s,f,d) = (q,[s],f,d1) where
  d1 q c= [d q c] 


-- Conversion from NFSM to FSM by the "subset construction"
nfsm_to_fsm :: Ord a => NFSM a -> FSM [a]
nfsm_to_fsm (q,s,f,d)=(power q,s,[x | x <- power q, overlap x f],d1) where
    d1 q a =nap_hat d q a

-- Similar conversion from EFSM to FSM using epsilon closure
efsm_to_fsm :: Ord a => EFSM a -> FSM [a]
efsm_to_fsm (qs,s,fs,trans,eps) = (q, eclose eps s,[x | x<- q, overlap x fs],d)  where
  q= power qs
  d q a = eap_hat (trans,eps) q a

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


accept2 :: Eq a=>FSM a-> [Char] -> Bool
accept2 (qs, s, fs, d)  = aux s  where
-- aux q w = whether the machine, starting in q, accepts w (recursive in w)
  aux q [] = q `elem` fs
  aux q (x:xs)= accept2 (qs,d q x,fs,d) xs

re2fsm :: RegExp -> FSM Int
re2fsm Empty = emptyFSM
re2fsm (Let c) = letterFSM c
re2fsm (Union r1 r2) = reduce $ unionFSM (re2fsm r1) (re2fsm r2)
re2fsm (Cat r1 r2) = reduce $ catFSM (re2fsm r1) (re2fsm r2)
re2fsm (Star r1) = reduce $ starFSM (re2fsm r1)

-- This test function will return a list of all strings that from sigma and accepted by the machine
test1 :: Ord a => FSM a->[String]
test1 m = [w| w <- strings 10, nacc nm w] where nm= fsm_to_nfsm m

test2 :: Ord a => NFSM a->[String]
test2 nm= [w| w <- strings 4, accept2 m w] where m= nfsm_to_fsm nm

test3 :: Ord a => EFSM a->[String]
test3 em= [w| w <- strings 4, accept2 m w] where m= efsm_to_fsm em

nm :: NFSM Int
nm= ([1,2,3,4], [1], [4], trans) where
  trans num ' ' = []
  trans 1 'a' = [1,2]
  trans 1 'b' = [1]
  trans 2 'a' = [3]
  trans 2 'b' = [3]
  trans 3 'a' = [4]
  trans 3 'b' = [4]
  trans 4 'a' = []
  trans 4 'b' = []



em :: EFSM Int
em = ([1,2,3,4], [1], [4], trans, [(2,3),(3,4)]) where
  trans num ' '= []
  trans 1 'a' = [1,2]
  trans 1 'b' = [1]
  trans 2 'a' = [4]
  trans 2 'b' = [4]
  trans 3 'a' = [1]
  trans 3 'b' = [1]
  trans 4 'a' = []
  trans 4 'b' = []

--------------------------------------------------------------------------------------------------------------------------------
{- Tests:


1. m and fsm_to_nfsm m accept the same strings

re= Cat (Let 'a') (Let 'b')
test1 (re2fsm re) = ["ab"]

re= Union (Let 'a') (Let 'b')
test1 (re2fsm re) = ["a","b"]

re=Star (Cat (Let 'a') (Let 'b'))

test1 (re2fsm re) = ["","ab","abab","ababab","abababab","ababababab"]

2. m and nfsm_to_fsm m accept the same strings

nm= ([1,2,3,4], [1], [4], trans) where
  trans 1 'a' = [1,2]
  trans 1 'b' = [1]
  trans 2 'a' = [3]
  trans 2 'b' = [3]
  trans 3 'a' = [4]
  trans 3 'b' = [4]

test2 nm = ["aaa","aab","aba","abb","aaaa","aaab","aaba","aabb","baaa","baab","baba","babb"]

3. m and efsm_to_fsm m accept the same strings

em = ([1,2,3,4], [1], [4], trans, [(2,3),(3,4)]) where
  trans 1 'a' = [1,2]
  trans 1 'b' = [1]
  trans 2 'a' = [3]
  trans 2 'b' = [3]
  trans 3 'a' = [1]
  trans 3 'b' = [1]
  trans 4 'a' = []
  trans 4 'b' = []

test3 em = ["a","aa","ab","ba","aaa","aab","aba","baa","bab","bba","aaaa","aaab","aaba","abaa","abab","abba","baaa","baab","baba","bbaa","bbab","bbba"]
-}