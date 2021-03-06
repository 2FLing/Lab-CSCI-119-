-- CSci 119, Lab 3

-- See https://hackage.haskell.org/package/base-4.14.0.0/docs/Data-List.html
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
{-# OPTIONS_GHC -Wno-deferred-type-errors #-}
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
----------------------------------------------------------
--test case:
-- cart ["hello"]["world"] => [("hello","world")]
-- cart ["a","b","c"] ["x","y","z"] => [("a","x"),("a","y"),("a","z"),("b","x"),("b","y"),("b","z"),("c","x"),("c","y"),("c","z")]
----------------------------------------------------------

-- Powerset, preserves normalization. Examples:
-- power [] = [[]]
-- power [1] = [[],[1]]
-- power [1,2] = [[],[1],[1,2],[2]]
-- power [2,3]= [[],[2],[2,3],[3]]
-- power [1,2,3] = [[],[1],[1,2],[1,2,3],[1,3],[2],[2,3],[3]]

power :: [a] -> [[a]]
power []=[[]]
power (x:xs)=
  let phead= [[]]
      pbody= map([x]++) $ power xs
      ptail=tail$ power xs
  in  phead++pbody++ptail
----------------------------------------------------------
--test case:
-- power ['a','b','c'] => ["","a","ab","abc","ac","b","bc","c"]
-- power ["how","much","money"] => [[],["how"],["how","much"],["how","much","money"],["how","money"],["much"],["much","money"],["money"]]
----------------------------------------------------------
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
----------------------------------------------------------
--test case:
-- lol "hello" => "hello"
-- lol  "wolrd" => "wolrd"
----------------------------------------------------------
-- Concatenation of LOLs, preserves invariant
dot :: LOL a -> LOL a -> LOL a
dot  (LOL _ l1) (LOL _ l2)=lol (l1++l2)
----------------------------------------------------------
--test case:
-- dot (lol "hello") (lol "world") => "helloworld"
-- dot (lol "a")(lol "bbbbb") => "abbbbb"
----------------------------------------------------------
-- Reverse of LOLs, preserves invariant
rev :: LOL a -> LOL a
rev (LOL _ l)=lol (reverse l) 
----------------------------------------------------------
--test case:
-- rev (lol "Hello") => "olleh"
-- rev (lol "Areukidding?") => "?gniddikuerA"
----------------------------------------------------------


---------------- Languages

-- Normalized lists of LOLs (aka "languages")
-- Invariant: xs :: Lang a implies xs is ordered with no duplicates
type Lang a = [LOL a]


-- Constructor for languages, establishes invariant
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs
----------------------------------------------------------
--test case:
-- lang ["hello","world"] => ["hello","world"]
-- lang ["yooo","hoooo"] => ["hoooo","yooo"]
----------------------------------------------------------
-- Membership for languages (infinite lists satisfying invariant included)
memb :: Ord a => LOL a -> Lang a -> Bool
memb a b = memHelper a $ sort b where 
  memHelper:: Ord a => LOL a -> Lang a -> Bool
  memHelper (LOL len l) ((LOL len_x l_x) : xs)
    | len < len_x = False
    | len == len_x && l == l_x = True
    | otherwise = memHelper (LOL len l) xs

----------------------------------------------------------
--test case:
-- memb (lol "hello")(lang ["hello","world"]) => True
-- memb (lol "he")(lang ["hello","world"]) => False
-- memb (lol "he")(lang ["I","you","she","he"]) => True
----------------------------------------------------------
-- Merge of langages (aka "union")
merge :: Ord a => Lang a -> Lang a -> Lang a
merge x []=x
merge [] y=y
merge (x:xs) (y:ys)=norm(x:y :merge xs ys)
----------------------------------------------------------
--test case:
-- merge (lang["hello"])(lang["world"]) => ["hello","world"]
-- merge (lang["I dont know"])(lang["me either"]) => ["me either","I dont know"]
----------------------------------------------------------
-- Concatenation of languages
cat :: Ord a => Lang a -> Lang a -> Lang a
cat [] y=[]
cat y []=[] 
cat xs ys = [dot a b|b<-ys,a<-xs]
----------------------------------------------------------
--test case:
-- cat (lang ["a","b"])(lang ["c","d"]) => ["ac","bc","ad","bd"]
-- cat (lang ["ab","ba"])(lang["cd","dc"]) => ["abcd","bacd","abdc","badc"]
----------------------------------------------------------
-- Kleene star of languages
kstar :: Ord a => Lang a -> Lang a
kstar [] = [eps]
kstar (LOL 0 []:xr) = kstar xr 
kstar xs = eps : cat xs (kstar xs)
----------------------------------------------------------
--test case:
-- take 10 $ kstar(lang ["a","bb"]) => ["","a","bb","aa","bba","abb","bbbb","aaa","bbaa","abba"]
-- take 5 $ kstar (lang ["d"]) => ["","d","dd","ddd","dddd"]
----------------------------------------------------------
-- Left quotient of a language by an LOL (cf. Definition 2.16)
-- Hint: Use the stripPrefix function
leftq :: Ord a => LOL a -> Lang a -> Lang a
leftq (LOL _ x) y=[lol (tail b)| (LOL _ b) <- y, stripPrefix x b /= Nothing] 
----------------------------------------------------------
--test case:
-- leftq (lol "hw") (lang ["hwyou","hwidk","hwyyy","hello"]) => ["widk","wyou","wyyy"]
-- leftq (lol "y")(lang ["mhy","ykk","lol"]) => ["kk"]
----------------------------------------------------------

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

----------------------------------------------------------
--test case:
-- toRE "ab+" => Union (Let 'a') (Let 'b')
-- toRE "abc+." => Cat (Let 'a') (Union (Let 'b') (Let 'c'))
----------------------------------------------------------

-- The one-string and finite languages of Theorem 3.2. It should be the case
-- that, for any string w, lang_of (onestr w) == [w], and for any (finite) list
-- of (distinct, sorted) strings l, lang_of (finite l) == l.
onestr :: String -> RegExp
onestr []= Empty
onestr [x]= Let x
onestr xs =  Cat (Let $ head xs) (onestr $ tail xs)
----------------------------------------------------------
--test case:
-- onestr "hello" => Cat (Let 'h') (Cat (Let 'e') (Cat (Let 'l') (Cat (Let 'l') (Let 'o'))))
-- onestr "mayday" => Cat (Let 'm') (Cat (Let 'a') (Cat (Let 'y') (Cat (Let 'd') (Cat (Let 'a') (Let 'y')))))
----------------------------------------------------------

--finite ["aba", "c"]
--Union (Cat (Let 'a') (Cat (Let 'b') (Let 'a'))) (Let 'c')
finite :: [String] -> RegExp
finite []= Empty
finite [x]= onestr x
finite xs =  Union (onestr $ head xs) (finite $ tail xs)
----------------------------------------------------------
--test case:
-- finite ["are","you"] => Union (Cat (Let 'a') (Cat (Let 'r') (Let 'e'))) (Cat (Let 'y') (Cat (Let 'o') (Let 'u')))
-- finite ["c","ddd"] => Union (Let 'c') (Cat (Let 'd') (Cat (Let 'd') (Let 'd')))
----------------------------------------------------------

-- The language associated to a regular expression, i.e., [[r]]

lang_of :: RegExp -> Lang Char
lang_of =lHelper  where
  lHelper Empty=[]
  lHelper (Let x)=lang[[x]]
  lHelper (Cat (Let x) (Let y))=lang[[x]++[y]]
  lHelper (Cat x y)=[dot a b | a<- lang_of x, b<- lang_of y]
  lHelper (Union x y)=lang_of x ++lang_of y
  lHelper (Star x)=kstar $ lang_of x
----------------------------------------------------------
--test case:
-- lang_of (Let 'c') =>["c"]
-- lang_of (Cat (Let 'c')(Let 'd')) => ["cd"]
-- lang_of (Union (Cat (Let 'c') (Let 'd'))(Cat (Let 'a')(Let 'b'))) => ["cd","ab"]
-- take 10 $ lang_of (Star (Union (Cat (Let 'c') (Let 'd'))(Cat (Let 'a')(Let 'b')))) => ["","cd","ab","cdcd","abcd","cdab","abab","cdcdcd","abcdcd","cdabcd"]
----------------------------------------------------------
-- Test all of the above operations extensively!            

