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

dom :: System -> [Perm]
dom system = [target | (target, _) <- system]

img :: System -> [Perm]
img system = [result | (_, result) <- system]

prm :: Int -> Perm
prm = map digitToInt . show

-- The symmetric group; i.e. permutations of {1,..,n}
sym :: Int -> [Perm]
sym n = permutations [1..n]

-- is there a nicer way?
partitions :: Ord a => [a] -> [[[a]]]
partitions xs = map tail $ par xs
  where 
    par [] = [[[]]]
    par ys = nub $ map sort [b:p | b <- bites ys, p <- par (ys \\ b)]
    bites [] = [[]]
    bites ys = nub $ map sort $ [y:p | y <- ys, p <- []:(bites $ delete y ys)]

-- these actions correspond to the core elements in the D_4, we can use them on
-- permutations by treating them as mesh patterns and applying elements to the
-- pattern
-- all elements in D_4
actions :: [Perm -> Perm]
actions = [id, actionH, actionV, actionR . actionH, actionR . actionV,
            actionR, actionR . actionR, actionR . actionR . actionR]
  where 
    actionH perm = map (\i -> length perm - i + 1) perm
    actionV = reverse
    actionR perm = one_line perm [length perm, length perm - 1..1]
    one_line xs ys = map snd $ sort (zip xs ys)

-- function to apply a given symmetry on a collection of equivalences
apply_symmetry :: (Perm -> Perm) -> [Equivalence] -> [Equivalence]
apply_symmetry action = map (nub . sort . map action) 

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
apply_rule (target, result) perm occ
  | standard prm_target == target 
    = Just $ take occ perm ++ lift (minimum prm_target - 1) result ++ drop (occ+length target) perm
  | otherwise = Nothing
  where 
    prm_target = take (length target) $ drop occ perm

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
confluence_counterexamples :: System -> [Perm]
confluence_counterexamples system = filter (not . same_test . map (normal_forms system) . try_apply system) domain_clusters 
  where 
    domain_clusters = sortOn length $ findSystemClusters system
    same_test xs = nub xs == [head xs]
    -- the O(R), R system, function in Ander's paper, the clusters of a systems domain
    findSystemClusters r = [c | p <- dom r, q <- dom r, c <- findClusters p q, not $ null c]

-- test whether a list of Ints in actually a permutation
is_permutation :: [Int] -> Bool
is_permutation s = all (\i -> count i s == 1) [1..length s]
  where 
    count x = length . filter (x==)

-- the O(r,s), r,s permutations, function in Ander's paper, given two permutation return a 
-- list of how they can cluster
findClusters :: Perm -> Perm -> [Perm]
findClusters p q = filter is_permutation matches
  where 
    max_len = max (length p) (length q)
    min_len = min (length p) (length q)
    squash s t i = s ++ (drop i t)
    matches = [squash (lift n p) q i | i <- [1..min_len-1], n <- [1..max_len-1], 
                                       ekat i (lift n p) == take i q]
            ++ [squash p (lift n q) i | i <- [1..min_len-1], n <- [1..max_len-1], 
                                       ekat i p == take i (lift n q)]

lenshr :: Perm -> Perm -> Int
lenshr p q 
  | null $ findClusters p q = 0
  | otherwise = maximum $ map (\cluster -> (length p + length q) - length cluster) $ findClusters p q

rule_check :: [Perm] -> Rule -> Bool
rule_check sys_image (t, r) = ekat m t == ekat m r
  where 
    m = maximum $ map (lenshr t) sys_image

joininvariance_check :: System -> Bool
joininvariance_check system = all (rule_check image) system
  where
    image = filter ((==3) . length) $ img system

windows :: Int -> [a] -> [[a]]
windows m xs = [take m $ drop n xs | n <- [0..length xs - m]]

sigma :: Perm -> Perm -> Int
sigma perm pattern = sum $ zipWith zipper [1..] $ windows (length pattern) perm
  where 
    zipper i w = if standard w == pattern then i else 0

sigma_sum :: Perm -> [Perm] -> Int
sigma_sum perm = sum . map (sigma perm)

delta_of_rule :: [Perm] -> Rule -> Int
delta_of_rule patterns (t,r) = sigma_sum r patterns - sigma_sum t patterns

confluentize :: [Perm] -> System -> Maybe System
confluentize patterns system
  | null counterexs = Just system
  | maximum (map (delta_of_rule patterns) rules) < 1 = Nothing
  | otherwise = confluentize patterns (system ++ [added_rule])
  where 
    counterexs = confluence_counterexamples system
    added_rule = maximumBy (comparing (delta_of_rule patterns)) rules 
    rules = [(r, t) | let forms = normal_forms system splitter, r <- forms, t <- delete r forms ]
    splitter = head counterexs

combos :: Ord a => [[a]] -> [[a]]
combos xss
  | _combos xss == [[]] = []
  | otherwise = _combos xss
  where
    _combos [] = [[]]
    _combos [[]] = [[]]
    _combos xs = if any (==[]) xs then [] else [a:b | a <- head xs, b <- _combos (tail xs)]

make_system :: [Equivalence] -> Maybe System
make_system = make_confluent_system . filter joininvariance_check . make_rewrite_systems 

make_rewrite_systems :: [Equivalence] -> [System]
make_rewrite_systems = map concat . combos . map make_single_image_systems 

make_single_image_systems :: Equivalence -> [System]
make_single_image_systems eq = [[(domain, image) | domain <- delete image eq] | image <- eq]

make_confluent_system :: [System] -> Maybe System
make_confluent_system = listToMaybe . filter joininvariance_check . sortOn length . mapMaybe (\sys -> confluentize (img sys) sys)

sym_partitions :: [[Equivalence]]
sym_partitions = tail $ map (filter (\p -> length p > 1)) $ partitions $ sym 3

doo :: [Maybe System] -> Maybe (System, Int)
doo syss
  | isNothing try_find = Nothing
  | otherwise = Just (fromJust $ syss !! (fromJust try_find), fromJust try_find)
  where try_find = findIndex isJust syss

trm_cfl_systems :: [([Equivalence], Maybe (System, Int))]
trm_cfl_systems = 
  filter (isJust . snd)
  $ map (\(a, b) -> (a, doo b))
  $ map (\(a, b) -> (a, map make_system b))
  $ map (\x -> (x,  get_all_turns x)) sym_partitions

main :: IO ()
main = do
    let to_print = map (\(e, d) -> (e, fromJust d)) $ ([],Just ([], 0)): trm_cfl_systems 
    let findSystemClustersDict sys = [((p, q), c) | p <- dom sys, q <- dom sys, c <- findClusters p q, not $ null c]

    mapM_ (\(e, (sys, i)) -> print (e, sys, dom sys, findSystemClustersDict sys, i)) to_print

