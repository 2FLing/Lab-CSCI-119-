-- CSci 119, Lab 4

import Data.List (sort, stripPrefix) -- for your solution to Lab 3


---------------- Code provided to you in Lab 3 ----------------

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Length-Ordered Lists over "character type" a (aka "strings")
-- Invariant: In LOL n xs, n == length xs
data LOL a = LOL Int [a] deriving (Eq,Ord)

instance Show a => Show (LOL a) where
  show (LOL n xs) = show xs

-- Empty list (epsilon)
eps :: LOL a
eps = LOL 0 []

-- Smart constructor for LOL a, establishes invariant
lol :: [a] -> LOL a
lol xs = LOL (length xs) xs

-- Normalized lists of LOLs (aka "languages")
-- Invariant: xs :: Lang a implies xs is sorted with no duplicates
type Lang a = [LOL a]

-- Smart constructor for (finite) languages
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs

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


---------------- Your solution to Lab 3 ----------------

-- Include here any code you need from your solution to Lab 3 for testing
-- purposes. After a few days, I will release my solution for you to use.
-- Don't duplicate the code just given above.

-- Concatenation of LOLs, preserves invariant
dot :: LOL a -> LOL a -> LOL a
dot  (LOL _ l1) (LOL _ l2)=lol (l1++l2)

-- Concatenation of languages
cat :: Ord a => Lang a -> Lang a -> Lang a
cat [] y=[]
cat y []=[] 
cat xs ys = [dot a b|b<-ys,a<-xs]

-- Kleene star of languages
kstar :: Ord a => Lang a -> Lang a
kstar [] = [eps]
kstar (LOL 0 []:xr) = kstar xr 
kstar xs = eps : cat xs (kstar xs)

-- Merge of langages (aka "union")
merge :: Ord a => Lang a -> Lang a -> Lang a
merge [] ys = ys
merge xs [] = xs
merge xs@(x:xr) ys@(y:yr) =
  case compare x y of
    LT -> x : merge xr ys
    EQ -> x : merge xr yr
    GT -> y : merge xs yr

-- The one-string and finite languages of Theorem 3.2. It should be the case
-- that, for any string w, lang_of (onestr w) == [w], and for any (finite) list
-- of (distinct, sorted) strings l, lang_of (finite l) == l.
onestr :: String -> RegExp
onestr []= Empty
onestr [x]= Let x
onestr xs =  Cat (Let $ head xs) (onestr $ tail xs)

--finite ["aba", "c"]
--Union (Cat (Let 'a') (Cat (Let 'b') (Let 'a'))) (Let 'c')
finite :: [String] -> RegExp
finite []= Empty
finite [x]= onestr x
finite xs =  Union (onestr $ head xs) (finite $ tail xs)

-- The language associated to a regular expression, i.e., [[r]]
lang_of :: RegExp -> Lang Char
lang_of Empty = []
lang_of (Let a) = lang [[a]]
lang_of (Union r1 r2) = merge (lang_of r1) (lang_of r2)
lang_of (Cat r1 r2) = cat (lang_of r1) (lang_of r2)
lang_of (Star r1) = kstar (lang_of r1)

---------------- Part 1 ----------------

-- Implement the seven recursive predicates/operations on RegExp given in
-- Section 3.3 of the notes; call them empty, unitary, byp, inf, rever, lq,
-- and nep. Each should begin with a type declaration. Include several tests
-- for each function.

empty :: RegExp -> Bool
empty x= null (lang_of x)

unitary :: RegExp -> Bool
unitary x= lang_of x ==lang [""]

byp :: RegExp -> Bool
byp Empty=False
byp (Let x)=False
byp (Star x)=True
byp (Union x y)=byp x || byp y
byp (Cat x y)=byp x && byp y

inf :: RegExp -> Bool
inf Empty=False
inf (Let x)=False
inf (Union x y)= inf x||inf y
inf (Cat x y)=(inf x && not (empty y)) || (inf y && not(empty x))
inf (Star x) = not (empty x) && not (unitary x)

rever :: RegExp -> RegExp 
rever Empty=Empty
rever (Let x)=Let x
rever (Union x y)=Union (rever x) (rever y)
rever (Cat x y)=Cat (rever y)(rever x)
rever (Star x)=Star (rever x)

lq :: Char -> RegExp -> RegExp
lq x Empty=Empty
lq x (Let y)= if x==y then Star Empty else Empty
lq x (Union y z)= Union (lq x y) (lq x z)
lq x (Cat y z)= if byp y then Cat (lq x y) z else Cat (lq x z) y
lq x (Star y)=Cat (lq x y) (Star y)

nep :: RegExp -> RegExp
nep Empty=Empty
nep (Let x)=Let x
nep (Union x y)= Union (nep x) (nep y)
nep (Cat x y)= if byp x then Union (Cat (nep x) y) (nep y) else Cat (nep x) y
nep (Star x) = Cat (nep x) (Star x)

---------------- Part 2 ----------------

-- Implement the two matching algorithms given in Section 3.4 of the notes,
-- where the second algorithm is the modified one I posted on Piazza (@96).
-- Call them match1 and match2. Start by implementing splits:

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "bc" =  [("","bc"), ("b","c"), ("bc","")]
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
splits :: [a] -> [([a], [a])]
splits []=[]
splits xs = if length xs==1 then splitHead xs++splitTail xs
else
  splitHead xs++splitBody x y++splitTail xs where
  x=[head xs]
  y= tail xs
  splitHead :: [a] -> [([a], [a])]
  splitHead xs=[([],xs)]
  splitBody :: [a] ->[a]-> [([a], [a])]
  splitBody x y= if not (null $ tail y)
          then (x,y):splitBody (x++[head y]) (tail y)
          else [(x,y)]
  splitTail :: [a] -> [([a], [a])]
  splitTail xs=[(xs,[])]


match1 :: RegExp -> String -> Bool
match1 r w = m1 r w where
  m1 :: RegExp -> String -> Bool
  m1 Empty w=False
  m1 (Let x) w= [x]==w
  m1 (Union x y) w= match1 x w || match1 y w
  m1 (Cat x y) w=or[match1 x (fst a) && match1 y (snd a)| a<-splits w]
  m1 (Star x) w= null w || or[match1 x (fst a) && match1 (Star x) (snd a) | a <- splits w, not (null $ fst a)]

             


match2 :: RegExp -> String -> Bool

match2 r w = m [r] False w where
  m :: [RegExp] ->Bool->String->Bool
  m [Empty] c w= not c && null w 
  m (Let x:rs) c w= x==head w && m rs (not c) (tail w)
  m ((Union r1 r2):rs) c w= m (r1:rs) c w || m (r2:rs) c w
  m ((Cat r1 r2):rs) c w= m (r1:r2:rs) c w || c && byp r1 && m (r2:rs) c w
  m (Star r1:rs) c w= (not c && m rs c w) || m (r1:Star r1:rs) c w

test :: [RegExp] ->Bool->String->Bool
test [Empty] c w= not c && null w 
test  (Let x:rs) c w= x==head w && test  rs (not c) (tail w)
test  ((Union r1 r2):rs) c w= test  (r1:rs) c w || test  (r2:rs) c w
test  ((Cat r1 r2):rs) c w= test  (r1:r2:rs) c w || c && byp r1 && test  (r2:rs) c w
test  (Star r1:rs) c w= (not c && test  rs c w) || test  (r1:Star r1:rs) c w
-- Some regular expressions for testing. Also, test them on other solutions
-- to the exercises of Section 3.2 (as many as you can get). 

sigma = ['a', 'b']                -- Alphabet used in all examples below

ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once


-- For your tests, you may also find the following helpful. For example,
-- you can generate all strings of length 10 (or 20) or less and then test
-- to see whether match1 r w == memb (lol w) (lang_of r) for each such w.

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concatMap str [0..n] where
  str 0 = [""]
  str n = [a:w | a <- sigma, w <- str (n-1)]