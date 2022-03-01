-- Boolean binary operation on FSMs. Examples:
-- binopFSM (||) m1 m2 computes union machine
-- binopFSM (&&) m1 m2 computes intersection machine
import Data.List

type BoolOp = Bool -> Bool -> Bool
type Trans a = a -> Char -> [a]
type FSM a = ([a], a, [a], a -> Char -> a)
type NFSM a = ([a], [a], [a], Trans a)

sigma :: [Char]
sigma = "ab"

(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

uclosure :: Ord a => [a] -> (a -> [a]) -> [a]
uclosure xs g = sort $ stable $ iterate close (xs, []) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') $ concatMap g fr

unionFSM :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a, b)
unionFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
        qs = qs1 >< qs2
        s  = (s1,s2)
        fs = [(a,b)| a<- fs1, b <- qs2]++[(a,b) | a <- qs1, b <- fs2]
        d = dh where
          dh (x,y) c =(d1 x c,d2 y c)

symdiff :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a,b)
symdiff a b = sh a b where
sh (q1,s1,fs1,d1) (q2,s2,fs2,d2)= (q1 >< q2, (s1,s2),([(a,b)| a<- fs1, b <- q2]++[(a,b) | a <- q1, b <- fs2])\\(fs1 >< fs2),d) where
              d (x1,x2) a = (d1 x1 a , d2 x2 a)

inters :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a,b)
inters a b = ih a b where
ih (q1,s1,fs1,d1) (q2,s2,fs2,d2)=(q1 >< q2,(s1,s2),fs1 >< fs2, d) where
    d (x1,x2) a = (d1 x1 a , d2 x2 a)

binopFSM :: (Eq a, Eq b) => BoolOp -> FSM a -> FSM b -> FSM (a,b)
binopFSM (||) m1 m2 = unionFSM m1 m2
binoFSM  (&&) m1 m2 = inters m1 m2 
binoFSM  (/=) m1 m2 = symdiff m1 m2
    

-- Reverse FSM to a NFSM. Output machine accepts reverse of language of input machine.
reverseFSM :: Eq a => FSM a -> NFSM a
reverseFSM m = rh m where
    rh (qs, s, fs, d) = (qs,fs,[s],trans) where
        trans q a =[x | x <- qs, d x a == q]

-- Reachable states of a NFSM (similar to reachable but on NFSMs)
nreachable :: Ord a => NFSM a -> [a]
nreachable  m@(qs, s, fs, trans) =  uclosure s (\q -> concatMap (trans q) sigma) 

--Remove Item from list
removeItem :: Ord a => a -> [a]->[a]
removeItem _ [] =[]
removeItem x (y:ys) = if x== y then removeItem x ys else y:removeItem x ys

--Remove a list of items from list
removeItems:: Ord a =>[a]->[a]->[a]
removeItems [] x=x
removeItems _ []=[]
removeItems (x:xs) ys= removeItems xs (removeItem x ys)

--get target for the enateRednt function which returns the redundant states in the NFSM
getT::Ord a => [(a,a)] ->[(a,a)]
getT []=[]
getT (x:xs)= [a | a<- xs, fst a== snd x, snd a ==fst x]++getT xs

--remove redundant states in the NFSM, such as [(1,2),(2,1)], we can basically remove (2,1)
enateRednt :: Ord a => [(a,a)] -> [(a,a)]
enateRednt [] =[]
enateRednt [x]=[x]
enateRednt l = removeItems target l where
  target= getT l

-- make those states of NFSM to be in ordered
clear::Ord a => NFSM (a,a) ->NFSM (a,a)
clear m@(qs,s,f,d) =(nqs,ns,f,d) where
  nqs=filter(uncurry(<)) qs
  ns= filter(uncurry(<)) s

existEqual:: Ord a => (a,a) -> [(a,a)] ->Bool
existEqual x l = or [(fst x == fst y && snd x == snd y) || (fst x == snd y && snd x == fst y)| y <- l]

sub::Ord a =>[a]->[a]->Bool
sub [] [] =True
sub _ [] =False
sub [] _ = True
sub (x:xs) (y:ys) = if x==y then sub xs ys else sub (x:xs) ys

remdup::Ord a =>[[a]]->[[a]]
remdup []=[]
remdup l = removeItems target l where
  target = [y | x <- l, y <- removeItems [x] l, sub y x]

makecomp:: Ord a=>[a]->[[a]]->[a]
makecomp x [y]=x\\y
makecomp x (y:ys)=makecomp (makecomp x [y]) ys

dmover ::Ord a => (a->Char->a)->[a]->Char->[[a]]->[a]
dmover d (y:ys) a (x:xs)= if d y a `elem` x then x else dmover d (y:ys) a xs  

-- Minimize a FSM. Put all of the above together to compute the minimum machine for m
minimize :: Ord a => FSM a -> FSM [a]
minimize m1@(qs,s1,f1,d1) = (q,s,f,d) where
  exclvor= binopFSM (/=) m1 m1
  rever@ (qs1,s2,f2,d2) = clear(reverseFSM exclvor)
  reachable=[x | x <- qs1, not (existEqual x (enateRednt(nreachable rever)))]
  groups=remdup$norm[fst x:[snd y | y <- reachable, fst y== fst x] | x <- reachable]
  comple=makecomp (removeItems f1 qs) groups
  q=if null comple then groups++[f1] else groups++[f1]++[comple]
  s=head q
  f=[f1]
  d (x:xs) a = dmover d1 (x:xs) a q


m :: FSM Int
m=([1,2,3,4],1,[2],d) where
  d 1 'a' =2
  d 1 'b' =4
  d 2 'a' =4
  d 2 'b' =3
  d 3 'a' =2
  d 3 'b' =4
  d 4 'a' =4
  d 4 'b' =4

m1 :: FSM Int
m1 = ([1,2,3,4],1,[3],d) where
  d 1 'a'=2
  d 1 'b'=3
  d 2 'a'=3
  d 2 'b'=4
  d 3 'a'=1
  d 3 'b'=2
  d 4 'a'=3
  d 4 'b'=4
  

-- Test. For example, make sure that the minimal machine agrees with the original machine
-- on lots of input strings. Try for multiple machines.
{-
test 1 

(qs,s,fs,d) = minimize m
  qs == [[1,3],[2],[4]]
  s == [1,3]
  fs == [[2]]
  [(q,a,d q a) | q <- qs, a <- sigma] == [([1,3],'a',[2]),([1,3],'b',[4]),([2],'a',[4]),([2],'b',[1,3]),([4],'a',[4]),([4],'b',[4])]

test 2
 qs1 = ["", "a", "b", "aa", "ab", "ba", "bb"]
 d1 q c = if length q < 2 then q ++ [c] else tail (q ++ [c])
 m = (qs1, "", ["ab"], d1) :: FSM String
 (qs,s,fs,d) = minimize m
 qs==[["","b","bb"],["a","aa","ba"],["ab"]]
 s==["","b","bb"]
 fs ==[["ab"]]
 [(q,a,d q a) | q <- qs, a <- sigma] == [(["","b","bb"],'a',["a","aa","ba"]),(["","b","bb"],'b',["","b","bb"]),(["a","aa","ba"],'a',["a","aa","ba"]),(["a","aa","ba"],'b',["ab"]),(["ab"],'a',["a","aa","ba"]),(["ab"],'b',["","b","bb"])]


 test 3

 (qs,s,fs,d) = minimize m1
  qs==[[2,4],[3],[1]]
  s==[2,4]
  fs==[[3]]
  [(q,a,d q a) | q <- qs, a <- sigma]==[([2,4],'a',[3]),([2,4],'b',[2,4]),([3],'a',[1]),([3],'b',[2,4]),([1],'a',[2,4]),([1],'b',[3])]
 -}