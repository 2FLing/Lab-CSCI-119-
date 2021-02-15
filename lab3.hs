-- CSci 119, Lab 3

-- See https://hackage.haskell.org/package/base-4.14.0.0/docs/Data-List.html
import Data.List (sort, stripPrefix)


---------------- General list functions

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Cartesian product, preserves normalization
cart :: [a] -> [b] -> [(a,b)]
cart a b= [(x,y) | x <-a, y <-b] 

-- Powerset, preserves normalization. Examples:
-- power [] = [[]]
-- power [1] = [[],[1]]
-- power [1,2] = [[],[1],[1,2],[2]]
-- power [2,3]= [[],[2],[2,3],[3]]
-- power [1,2,3] = [[],[1],[1,2],[1,2,3],[1,3],[2],[2,3],[3]]
power :: Ord a => [a] -> [[a]]
power []=[[]]
power (x:xs)= sort(power xs++[x:ys | ys <- power xs])



---------------- Length-ordered lists

-- Length-Ordered Lists over "character type" a (aka "strings over a")
-- Invariant: In LOL n xs, n == length xs
-- Note that automatically-derived Ord instance correctly orders LOLs
data LOL a = LOL Int [a] deriving (Eq, Ord)

-- Alternative Show instance that hides length
instance Show a => Show (LOL a) where
  show (LOL n xs) = show xs
  
-- Empty list (epsilon)
eps :: LOL a
eps = LOL 0 []

-- Smart constructor for LOL a, establishes invariant
lol :: [a] -> LOL a
lol xs = LOL (length xs) xs

-- Concatenation of LOLs, preserves invariant
dot :: LOL a -> LOL a -> LOL a
dot  (LOL _ l1) (LOL _ l2)=lol (l1++l2)
-- Reverse of LOLs, preserves invariant
rev :: LOL a -> LOL a
rev (LOL _ l)=lol (reverse l) 



---------------- Languages

-- Normalized lists of LOLs (aka "languages")
-- Invariant: xs :: Lang a implies xs is ordered with no duplicates
type Lang a = [LOL a]


-- Constructor for languages, establishes invariant
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs

-- Membership for languages (infinite lists satisfying invariant included)
memb :: Ord a => LOL a -> Lang a -> Bool
memb (LOL len l) b = not (or [len < len_a | (LOL len_a l_a) <- sort b])
                    && or [l == l_a | (LOL len_a l_a) <- sort b]
                   

-- Merge of langages (aka "union")
rmdups ::  Eq a =>  [a] -> [a]
rmdups [] = []
rmdups (x:xs)=x : filter(/=x) (rmdups xs)

merge :: Ord a => Lang a -> Lang a -> Lang a
merge x y = sort $ rmdups (x++y)

-- Concatenation of languages
cat :: Ord a => Lang a -> Lang a -> Lang a
cat x y = sort $ rmdups [lol (lx++ly)| (LOL _ lx) <- x,(LOL _ ly)<-y]

-- Kleene star of languages
kstar :: Ord a => Lang a -> Lang a
kstar [] = [eps]
kstar (LOL 0 []:xr) = kstar xr 
kstar xs = eps : cat xs (kstar xs)

-- Left quotient of a language by an LOL (cf. Definition 2.16)
-- Hint: Use the stripPrefix function
leftq :: Ord a => LOL a -> Lang a -> Lang a
leftq (LOL _ x) y=[lol (tail b)| (LOL _ b) <- y, stripPrefix x b /= Nothing] 


---- Regular expressions and the languages they denote 
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
    sp d Empty         = showString "0"
    sp d (Let c)       = showString [c]
    sp d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                         sp 6 r1 .
                         showString "+" .
                         sp 6 r2
    sp d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                         sp 7 r1 .
                         sp 7 r2
    sp d (Star Empty)  = showString "1"
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


-- The one-string and finite languages of Theorem 3.2. It should be the case
-- that, for any string w, lang_of (onestr w) == [w], and for any (finite) list
-- of (distinct, sorted) strings l, lang_of (finite l) == l.
onestr :: String -> RegExp
onestr xs = 

finite :: [String] -> RegExp
finite xs = undefined


-- The language associated to a regular expression, i.e., [[r]]
lang_of :: RegExp -> Lang Char
lang_of rs = lang [show rs]


-- Test all of the above operations extensively!            
