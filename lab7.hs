-- Lab 7: Convert FSMs to regular expressions

import Data.List
import Control.Monad (replicateM)  -- for strings function below


---------------- Given functions ----------------

-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concat $ [replicateM i sigma | i <- [0..n]]

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

-- Extended regular expressions, including a name for One = Star Empty,
-- and arbitrary numbers of arguments for (associative) Union and Cat
data RegExp' = Zero | One | Let' Char |
               Union' [RegExp'] | Cat' [RegExp'] | Star' RegExp'
  deriving (Eq, Ord, Show)

-- Convert ordinary RegExps into extended REs
fromRE :: RegExp -> RegExp'
fromRE Empty = Zero
fromRE (Let c) = Let' c
fromRE (Union r1 r2) = Union' [fromRE r1, fromRE r2]
fromRE (Cat r1 r2) = Cat' [fromRE r1, fromRE r2]
fromRE (Star r1) = Star' (fromRE r1)

-- Convert extended REs into ordinary REs, eliminating Union' and Cat' on
-- lists of length < 2, and right-associating them on longer lists
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

-- Basic postfix parser for RegExp', assuming binary + and ., for testing
toRE' :: String -> RegExp'
toRE' w = go w [] where
  go [] [r] = r
  go ('0':xs) rs = go xs (Zero:rs)
  go ('1':xs) rs = go xs (One:rs)
  go ('+':xs) (r2:r1:rs) = go xs (Union' [r1,r2]:rs)
  go ('.':xs) (r2:r1:rs) = go xs (Cat' [r1,r2]:rs)
  go ('*':xs) (r:rs) = go xs (Star' r:rs)
  go (x:xs) rs = go xs (Let' x:rs)


-- Finite state machines (as records), indexed by the type of their states
type FSM a = ([a], a, [a], a -> Char -> a)



---------------- Lab 7 begins here ----------------


-- Check for proper (cannot recognize epsilon)
proper :: RegExp' -> Bool
proper r = rh r where
  rh Zero = False
  rh One = False
  rh (Let' c)=True
  rh (Cat' l)= and [proper x | x <- l]
  rh (Union' l)= and [proper x | x <- l]
  rh (Star' r)=False

-- Solve a system of proper linear equations
-- You can assume that the system is correctly formed and proper
solve :: [[RegExp']] -> [RegExp'] -> [RegExp']

solve [] [] = []
solve ((l11:l1J) : rows) (l1':lI') = simp x1 : xI where
  -- l11 is the corner element, and l1J = [l12,...,l1n] is the rest of 1st row
  -- rows are the rest of the rows [[l21,...,l2n], ..., [ln1,...,lnn]]
  -- l1' is the first constant
  -- lI' are the rest of the contants [l2',...,ln']
  
  -- first column [l21, ..., ln1]
  lI1 = [ head x | x <- rows]

  -- sub-matrix [[l22,...,l2n], ..., [ln2,...,lnn]]
  lIJ = [tail x | x <- rows]
  --LIJ=li1xl11*xl1jUlij
  -- [[l22_bar,...,l2n_bar], ..., [ln2_bar,...,lnn_bar]] computed via (6)          
  lIJ_bar = zipWith sixes lI1 lIJ            -- loops for i = 2 .. n                                           
  sixes li1 liJ = zipWith (six li1) l1J liJ  -- loops for j = 2 .. n                                           
  six li1 l1j lij = Union'[Cat'[li1,Star' l11, l1j],lij]                                                        
                                                                            
  -- [l2'_bar,..., ln'_bar] computed via (7)
  lI'_bar = zipWith seven lI1 lI'                                                
  seven li1 li' = Union'[Cat'[li1, Star' l11,l1'],li']                             
    
  -- recursively solve the system of size n-1
  xI = solve lIJ_bar lI'_bar

  -- compute x1 from xI via (5)
  x1 = Cat'[Star' l11,Union'[Union'[Cat'[fst a, snd a]| a<- zip l1J xI],l1']]    
-- Generate a regular SPLE from an FSM via formulas in Theorem 6.5
toSPLE :: FSM Int -> ([[RegExp']], [RegExp'])
toSPLE (qs,s,fs,d) = (lIJ, lI') where
  
  -- Construct matrix of coefficients (coef i j = Lij)
  lIJ = [[simp (coef i j) | j <- qs] | i <- qs]
  coef i j = coefh sigma i j where
  coefh :: [Char]->Int->Int->RegExp'
  coefh [] i j=Zero
  coefh (x:xs) i j= if d (qs!!i) x== qs!!j then Let' x else coefh xs i j
    

  -- Construct constants
  lI' = [ if x `elem` fs then One else Zero | x <- qs]


-- Convert an FSM to a RegExp'
conv :: FSM Int -> RegExp'
conv m@(_,s,_,_) = simp $ solution !! s where
  (matrix, consts) = toSPLE m
  solution = solve matrix consts


-- Test! Test! Test! (and show your tests here)
{----------------------------------------------------------------------------
test 1 :
   input: 
   soln = let a = Let' 'a' ; b= Let' 'b' in solve [[ b, Zero, a], [a,b,Zero] ,[Zero, a, b]] [Zero, One, Zero]
   map (Compact . fromRE') soln

  output:
  [b*a(b+ab*ab*a)*ab*,b*ab*a(b+ab*ab*a)*ab*+b*,(b+ab*ab*a)*ab*]

test 2:
  input: 
  soln = let a = Let' 'a' ; b= Let' 'b' in solve [[ b, a, Zero], [Zero,b,a] ,[a,Zero,b]] [Zero, One, Zero]  
  map (Compact . fromRE') soln

  output:
  [b*ab*+b*ab*a(b+ab*ab*a)*ab*ab*,b*a(b+ab*ab*a)*ab*ab*+b*,(b+ab*ab*a)*ab*ab*]

test 3:
  input: 
  soln = soln = let a = Let' 'a' ; b= Let' 'b' in solve [[ b, a, Zero], [Zero,b,a] ,[a,Zero,b]] [One, Zero , Zero] 
  map (Compact . fromRE') soln

  output:
  [b*ab*a(b+ab*ab*a)*ab*+b*,b*a(b+ab*ab*a)*ab*,(b+ab*ab*a)*ab*]

test 4:
  input: 
  soln = let a = Let' 'a' ; b= Let' 'b' in solve [[ b, a, Zero], [Zero,b,a] ,[a,Zero,b]] [Zero, Zero , One]
  map (Compact . fromRE') soln

  output:
  [b*ab*a(b+ab*ab*a)*,b*a(b+ab*ab*a)*,(b+ab*ab*a)*]

----------------------------------------------------------------------------}
---------------- Lab 7 ends here ----------------------------------


{----------------------------------------------------------------------------
| Bonus feature:  A regular-expression simplifier
|----------------------------------------------------------------------------

A "simplified" RegExp' satisfies the following conditions:
(1) Every Union' is applied to a normalized list of two or more arguments,
    each of which is a One, Let', Cat', or Star' (i.e., not Zero or Union')
(2) Every Cat' is applied to a list of two or more arguments, each of which is
    a Let' or Star' (i.e., not Zero, One, Union', or Cat')
(3) Every Star' is applied to a Let', Union', or Cat' (i.e., not Zero, One,
    or Star')

The following simplification rules, when applied repeatedly at every subterm
of a RegExp' until it no longer changes, result in a simplified RegExp':

   Union' []                          --> Zero
   Union' [r]                         --> r
   Union' (rs1 ++ [Zero] ++ rs2)      --> Union' (rs1 ++ rs2)
   Union' (rs1 ++ [Union' rs] ++ rs2) --> Union' (rs1 ++ rs ++ rs2)
   Union' rs                          --> Union' (norm rs)                  (*)

   Cat' []                            --> One
   Cat' [r]                           --> r
   Cat' (rs1 ++ [Zero] ++ rs2)        --> Zero
   Cat' (rs1 ++ [One] ++ rs2)         --> Cat' (rs1 ++ rs2)
   Cat' (rs1 ++ [Union' rs] ++ rs2)   --> Union' (map (\r -> Cat' (rs1 ++ [r] ++ rs2)) rs)
   Cat' (rs1 ++ [Cat' rs] ++ rs2)     --> Cat' (rs1 ++ rs ++ rs2)

   Star' Zero                         --> One
   Star' One                          --> One
   Star' (Star' r)                    --> Star' r

(*) Note: this rule should only be applied if rs is not already normalized;
    normalization is used to realize the commutativity and idempotency of union
    (i.e., that  L1 u L2 = L2 u L1  and  L u L = L ).


However, it would be very inefficient to attempt to apply these rules in the
manner indicated. Instead, our approach is to stage the application of these
rules carefully to minimize the number of traversals of the regular expression.
-------------------------------------------------------------------------------}

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
