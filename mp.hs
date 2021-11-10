import Data.Maybe
import Data.List
import Data.Ord
import Data.Char

-- we differentiate between Perm=Permutation and [Int], 
-- [Int] is a permutation slice, which is not necesarily a valid
-- permutation, like [7,6,8]
-- We expect Perm to be a normalized, a permutation of [1..n]
type Perm = [Int]
type Rule = (Perm, Perm)
type System = [Rule]
type Equivalence = [Perm]

length_sort :: Ord a => [[a]] -> [[a]]
length_sort = (sortBy . comparing) length 

dom :: System -> [Perm]
dom system = [target | (target, _) <- system]

img :: System -> [Perm]
img system = [result | (_, result) <- system]

-- these two functions are just for testing
-- they work for permutations up to length 9
prm :: Int -> Perm
prm = map digitToInt . show

rule :: Int -> Int -> (Perm, Perm)
rule r s = (prm r, prm s)

-- best case, we make Perm, Rule, etc. a newtype with show instances
-- but this will do for now
show_prm :: Perm -> String
show_prm prm = if maximum prm < 10 
                then prm >>= show 
                else intercalate "," $ map show prm

show_rule :: Rule -> String
show_rule (t, r) = show_prm t ++ " \\rightarrow " ++ show_prm r 

show_sys :: System -> String
show_sys = unlines . map show_rule

show_eq :: Equivalence -> String
show_eq = show 

-- The symmetric group; i.e. permutations of {1,..,n}
sym :: Int -> [Perm]
sym n = permutations [1..n]

-- is there a nicer way?
partitions :: Ord a => [a] -> [[[a]]]
partitions xs = map tail $ par xs
    where par [] = [[[]]]
          par ys = nub $ map sort [b:p | b <- bites ys, p <- par (ys \\ b)]
          bites [] = [[]]
          bites ys = nub $ map sort $ [y:p | y <- ys, p <- []:(bites $ delete y ys)]

-- these actions correspond to the core elements in the D_4, we can use them on
-- permutations by treating them as mesh patterns and applying elements to the
-- pattern
actionH :: Perm -> Perm
actionH perm = map (\i -> length perm - i + 1) perm

actionV :: Perm -> Perm
actionV = reverse

actionR :: Perm -> Perm
actionR perm = one_line perm [length perm, length perm - 1..1]
    where one_line xs ys = map snd $ sort (zip xs ys)

-- all elements in D_4
actions :: [Perm -> Perm]
actions = [id
          ,actionR
          ,actionR . actionR
          ,actionR . actionR . actionR
          ,actionH
          ,actionV
          ,actionR . actionH
          ,actionR . actionV
          ]

-- function to apply a given symmetry on a collection of equivalences
apply_symmetry :: (Perm -> Perm) -> [Equivalence] -> [Equivalence]
apply_symmetry action = map (nub . sort . map action) 

-- can this be done nicer?
-- given a a list of collections of equivalence relations we find if they appear
-- again as a rotation/reverse/... and return the representives (WORD BETTER)
find_core :: [[Equivalence]] -> [[Equivalence]]
find_core [] = []
find_core [[]] = []
find_core [[[]]] = []
find_core (e:equivs) = e:find_core h
    where a = filter (/= (apply_symmetry actionH) e) equivs
          b = filter (/= (apply_symmetry actionV) e) a
          c = filter (/= (apply_symmetry actionR) e) b
          d = filter (/= (apply_symmetry (actionR . actionR)) e) c
          f = filter (/= (apply_symmetry (actionR . actionR . actionR)) e) d
          g = filter (/= (apply_symmetry (actionR . actionH)) e) f
          h = filter (/= (apply_symmetry (actionR . actionV)) e) g

-- all possible symmetries of a collection of equivalence relation 
get_all_turns :: [Equivalence] -> [[Equivalence]]
get_all_turns equivs = map ($ equivs) $ map apply_symmetry actions 

-- utility functions for finding clusters and applying rules
-- might copy anders' algorithm applying rules though
standard :: [Int] -> Perm
standard s = map (\e -> e - minimum s + 1) s
      
ekat :: Int -> [a] -> [a]
ekat n xs = drop (length xs - n) xs

lift :: Int -> Perm -> [Int]
lift n = map (+n)

apply_rule :: Rule -> Perm -> Int -> Maybe Perm
apply_rule (target, result) prm occ = 
    if standard prm_target == target 
        then Just $ take occ prm ++ lift (minimum prm_target - 1) result ++ drop (occ+length target) prm
        else Nothing
    where prm_target = take (length target) $ drop occ prm

try_apply :: System -> Perm -> [Perm]
try_apply system perm = catMaybes [apply_rule rule perm i | i <- [0..length perm-2], rule <- system]

-- find normal forms of a permutation given a system
-- if the system is non-terminating this computation might not end
normal_forms :: System -> Perm -> [Perm]
normal_forms system perm = 
  case try_apply system perm of
      [] -> [perm]
      perms -> nub (perms >>= normal_forms system)

-- this is Lemma 3.3
-- given a system returns a list pairs, first values being clusters of its domain
-- and second values being a boolean, whether applying one rule from the system
-- to the permutation will have the same normal form as each other (or the
-- original permutation) ????? (DO LATER)
test_confluence :: System -> [(Perm, Bool)]
test_confluence system = zip domain_clusters 
                $ map (\l -> nub l == [head l]) 
                $ map (map (normal_forms system)) 
                $ map (try_apply system) domain_clusters
    where domain_clusters = length_sort $ findSystemClusters system

-- test whether a list of Ints in actually a permutation
is_permutation :: [Int] -> Bool
is_permutation s = all (\i -> count i s == 1) [1..length s]
    where count x = length . filter (x==)

-- the O(r,s), r,s permutations, function in Ander's paper, given two permutation return a 
-- list of how they can cluster
findClusters :: Perm -> Perm -> [Perm]
findClusters s t = filter is_permutation matches
    where max_len = max (length s) (length t)
          min_len = min (length s) (length t)
          squash s t i = s ++ (drop i t)
          matches = [squash (lift n s) t i | i <- [1..min_len-1], 
                                             n <- [1..max_len-1], 
                                             ekat i (lift n s) == take i t]
                  ++ [squash s (lift n t) i | i <- [1..min_len-1], 
                                              n <- [1..max_len-1], 
                                           ekat i s == take i (lift n t)]

-- the O(R), R system, function in Ander's paper, the clusters of a systems
-- domain
findSystemClusters :: System -> [Perm]
findSystemClusters r = [c | p <- dom r, q <- dom r, c <- findClusters p q, not $ null c]

--right_moving_subpattern :: Perm -> Perm -> Bool
--right_moving_subpattern p q = map (\f -> f p < f q) (map sigma shared_subpatterns)
--    where shared_subpatterns = windows p `intersection` windows q

-- this needs to be for all equivalences
goodness_test :: Equivalence -> Perm -> Maybe Perm
goodness_test [[2,1,3],[1,3,2]] [1,3,2] = Just [1,3,2]
goodness_test [[1,3,2],[2,1,3]] [1,3,2] = Just [1,3,2]
goodness_test [[2,3,1],[3,1,2]] [3,1,2] = Just [3,1,2]
goodness_test [[3,1,2],[2,3,1]] [3,1,2] = Just [3,1,2]
goodness_test [[1,3,2],[2,1,3],[2,3,1],[3,1,2]] [3,1,2] = Just [1,3,2]
goodness_test eq p = if null $ concatMap (\q -> if q !! 2 == p !! 2 then [] else findClusters q p) (delete p eq) then Just p else Nothing

-- friend_clusters
good_images :: Equivalence -> [Perm]
good_images eq = mapMaybe (goodness_test eq) eq

-- given a terminating system, try to make it confluent
confluentize :: System -> Maybe System
confluentize system
  | all snd con = Just system
  | last system == added_rule = Nothing
  | otherwise = confluentize (system ++ [added_rule])
  where con = test_confluence system
        added_rule = (head $ try_apply system splitter, last $ try_apply system splitter)
        splitter = fst $ head $ filter (not . snd) con

windows :: Int -> [a] -> [[a]]
windows m = foldr (zipWith (:)) (repeat []) . take m . tails

offset :: (Eq a, Num a) => [a] -> [a] -> Maybe a
offset xs ys =
  case nub (zipWith (-) xs ys) of
    [d] -> Just d
    _ -> Nothing

occurrences :: Perm -> Perm -> [(Int, Perm)]
occurrences xs p =
  catMaybes $
  zipWith (\i v -> (i, v) <$ offset p v)
      [0..]
      (windows (length p) xs) 

sigma :: Perm -> Perm -> Int
sigma p w = sum $ map (succ . fst) $ occurrences w p

mult_sigma ps w = sum $ map (flip sigma w) ps

ssigma ps w =  sum $ zipWith (*) (map (base^) [0..]) $ reverse $ sigma_list ps w
    where base = (length w) * (length w - 1) `div` 2
          sigma_list ps w = map (flip sigma w) ps

sigma_of_rule :: [Perm] -> Rule -> Int
sigma_of_rule p (r,t) = mult_sigma p t - mult_sigma p r

confluentize_alt :: System -> Maybe System
confluentize_alt system
  | all snd con = Just system
  | last system == added_rule = Just system
  | maximum (map (sigma_of_rule (img system)) rules) == 0 = Nothing
  | otherwise = confluentize_alt (system ++ [added_rule])
  where con = test_confluence system
        added_rule = maximumBy (comparing (sigma_of_rule (img system))) rules 
        rules = [(r,t) | let forms = normal_forms system splitter, r <- forms, t <- delete r forms ]
        splitter = head [ w | n<-[1..], w <- sym n, length (normal_forms system w) > 1 ]


combos :: Ord a => [[a]] -> [[a]]
combos [] = [[]]
combos [[]] = [[]]
combos xs = if any (==[]) xs then [] else [a:b | a <- head xs, b <- combos (tail xs)]

make_system :: [Equivalence] -> Maybe System
make_system = make_cfl_system . make_terminating_systems 

make_system_alt :: [Equivalence] -> Maybe System
make_system_alt = make_cfl_system_alt . make_terminating_systems 

-- given a collection of equivalences we return a list of possible terminating
-- systems
make_terminating_systems :: [Equivalence] -> [System]
make_terminating_systems equivs = map concat $ if combos rules == [[]] then [] else combos rules
    where make_rules eq image = map (\x -> (x, image)) (delete image eq)
          rules = map (\eq -> map (make_rules eq) $ good_images eq) equivs

make_cfl_system :: [System] -> Maybe System
make_cfl_system [] = Nothing
make_cfl_system systems = listToMaybe $ length_sort confluent_systems
    where confluent_systems = mapMaybe confluentize systems

make_cfl_system_alt :: [System] -> Maybe System
make_cfl_system_alt [] = Nothing
make_cfl_system_alt systems = listToMaybe $ length_sort confluent_systems
    where confluent_systems = mapMaybe confluentize_alt systems

alls = tail $ map (filter (\p -> length p > 1)) $ partitions $ sym 3

test = 
  filter (isJust . snd)
  $ map (\(a, b) -> (a, listToMaybe $ catMaybes b))
  $ map (\(a, b) -> (a, map make_system b))
  $ map (\x -> (x, get_all_turns x)) alls

test2 = 
  filter (isJust . snd)
  $ map (\(a, b) -> (a, listToMaybe $ catMaybes b))
  $ map (\(a, b) -> (a, map make_system_alt b))
  $ map (\x -> (x, get_all_turns x)) (alls \\ (map fst test))

main = do
    let ok2 = map (\(e, d) -> (e, fromJust d)) $ ([],Just []): test ++ test2

    mapM_ putStrLn 
        $ map (\(e, d) -> 
            "(" ++ (show e) 
                ++ ", " ++ (show $ map show_rule d) 
                ++ "," ++ (show $ dom d) 
                ++ ", " ++ (show [((p, q), c) | p <- dom d, q <- dom d, c <- findClusters p q, not $ null c]) 
                ++ ")") $ ok2

