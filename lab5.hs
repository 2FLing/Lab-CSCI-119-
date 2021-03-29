-- CSci 119, Lab 5
-- Reference: Lecture notes, Sections 4.1, 4.2

import Data.List (isInfixOf, isSuffixOf)  -- useful for testing in Part 2

-- Again, for this (and most) labs, the alphabet will be {a,b} to keep testing
-- easier, but your code should work just as well for any finite list.
sigma = ['a', 'b']

-- Finite State Machine M = (Q, s, F, d) with integer states
type FSM = ([Int], Int, [Int], Int -> Char -> Int)


---------------- Part 1: Representing FSMs

-- Check whether a finite state machine (qs, s, fs, d) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (s is in qs)
-- (3) Final states are states (fs is a subset of qs)
-- (4) Transition function d gives a state in qs for every state in qs and
--     letter from sigma

unique :: Eq a => [a] -> Bool
unique []=True
unique (x:xs)= notElem x xs && unique xs

subset :: (Foldable t, Eq a) => [a] -> t a -> Bool
subset xs ys= and [ x `elem` ys | x <- xs]

trasnsition :: Eq a => (a -> Char -> a) -> [a] -> Bool
trasnsition d qs= and [d q c `elem` qs | q <- qs, c <- sigma]

checkFSM :: FSM -> Bool
checkFSM (qs, s, fs, d) = unique qs &&  elem s qs && subset fs qs && trasnsition d qs

-- Gives the delta* function (recursive in w)
dstar :: FSM -> Int -> [Char] -> Int
dstar m q w = dh m q w where
  dh:: FSM -> Int -> [Char] -> Int
  dh (qs, s, fs, d) q []= q
  dh (qs, s, fs, d) q (a:rw) = dh m (d q a) rw

-- Machine acceptance, Definition 1 (via delta*)
accept1 :: FSM -> [Char] -> Bool
accept1 m w = ah m w where
  ah :: FSM -> [Char] -> Bool
  ah (qs, s, fs, d) w = dstar m s w `elem` fs

-- Machine acceptance, Definition 2 (via L_q(M))
accept2 :: FSM -> [Char] -> Bool
accept2 (qs, s, fs, d) w = aux s w where

  -- aux q w = whether the machine, starting in q, accepts w (recursive in w)
  aux :: Int -> [Char] -> Bool
  aux q [] = q `elem` fs
  aux q (x:xs)= accept2 (qs,d q x,fs,d) xs


---------------- Part 2: FSM construction

-- Define a machine that accepts exactly the strings with an odd number of b's
-- (Solution given for illustration)
oddbs :: FSM
oddbs = ([0,1], 0, [1], d) where
  d q 'a' = q        -- stay in the same state
  d q 'b' = 1 - q    -- switch states

-- Define a machine that accepts exactly the strings that do not contain "aab"
-- as a substring and test it adequately
avoid_aab :: FSM
avoid_aab = ([0,1,2,3],0,[0,1,2],d) where
  d q 'a'= if q==0 then 1 else if q==1 then 2 else q
  d q 'b'= if q==0 then q else if q==1 then 0 else 3

-- Define a machine that accepts all strings that end in "ab" and test
end_ab :: FSM
end_ab = ([0,1,2],0,[2],d) where
  d q 'a'= 1
  d q 'b'= if q==1 then 2 else 0

-- Define a function that takes a string and returns a machine that accepts
-- exactly that string and nothing else (compare to 'onestr' from Lab 3)
-- Hint: the expression w ! i gives the i-th character of the string w
exactly :: String -> FSM
exactly w = (res,0, [last res], d) where
  res=reverse$ generate_list (length w) where
    generate_list:: Int ->[Int]
    generate_list 0=[0]
    generate_list x=x:generate_list (x-1)
  d q c=if q> length w -1 then length w +1 else if w!!q==c then q+1 else length w+1


-- Test the machines above. Also, try out the exerices at the end of Section 3.2
-- in my notes as FSMs. Do they produce the same results as your RegExp's did?

-- Recursive reimplementation of strings function from Lab 4
strings :: Int -> [String]
strings n = concat [strs i | i <- [0..n]] where
  strs 0 = [""]
  strs n = [a:xs | a <- sigma, xs <- strs (n-1)]

s10 :: [String]
s10 = strings 10  -- or larger, if you like

s6 :: [String]
s6 = strings 6
oddbs_test :: Bool
oddbs_test = and [accept1 oddbs w == odd (num_bs w) | w <- s10] && and [accept2 oddbs w == odd (num_bs w) | w <- s10] where
  num_bs w = sum (map (\x -> if x == 'b' then 1 else 0) w)

avoid_aab_test :: Bool
avoid_aab_test= and [accept1 avoid_aab w == not (isInfixOf "aab" w) | w <- s10] && and [accept2 avoid_aab w == not (isInfixOf "aab" w) | w <- s10]

end_ab_test :: Bool
end_ab_test= and [accept1 end_ab w==(isSuffixOf "ab" w) | w <- s10] && and [accept1 end_ab w==(isSuffixOf "ab" w) | w <- s10]
  
exactly_test :: Bool
exactly_test= and [w==b | w <- s6,b <- s6,accept1 (exactly w) b]