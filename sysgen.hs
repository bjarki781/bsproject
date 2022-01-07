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

-- auxillary function for testing, allows us to write (prm 123) instead of [1,2,3]
prm :: Int -> Perm
prm = map digitToInt . show

-- The symmetric group; i.e. permutations of {1,..,n}
sym :: Int -> [Perm]
sym n = permutations [1..n]

-- partitions of a set, could be nicer if implemented with Set instead of List
partitions :: Ord a => [a] -> [[[a]]]
partitions xs = map tail $ par xs
  where 
    par [] = [[[]]]
    par ys = nub $ map sort [b:p | b <- bites ys, p <- par (ys \\ b)]
    bites [] = [[]]
    bites ys = nub $ map sort $ [y:p | y <- ys, p <- []:(bites $ delete y ys)]

-- utility functions for finding clusters and applying rules
standard :: [Int] -> Perm
standard s = map (\e -> e - minimum s + 1) s
      
-- take from the end, reverse take
ekat :: Int -> [a] -> [a]
ekat n xs = drop (length xs - n) xs

lift :: Int -> Perm -> [Int]
lift n = map (+n)

-- given a rule, a permutation and an index into the permutation, try to apply
-- the rule on the permutation indexed by the index
apply_rule :: Rule -> Perm -> Int -> Maybe Perm
apply_rule (target, result) perm occ
  | standard prm_target == target 
    = Just $ take occ perm ++ lift (minimum prm_target - 1) result ++ drop (occ+length target) perm
  | otherwise = Nothing
  where 
    prm_target = take (length target) $ drop occ perm

-- try to apply all rules in a system to a permutation and return a list of successful applications
try_apply :: System -> Perm -> [Perm]
try_apply system perm = catMaybes [apply_rule rule perm i | i <- [0..length perm-2], rule <- system]

-- find normal forms of a permutation given a system
-- if the system is non-terminating this computation might not end
normal_forms :: System -> Perm -> [Perm]
normal_forms system perm = 
  case try_apply system perm of
      [] -> [perm]
      perms -> nub (perms >>= normal_forms system)

-- this is basically Lemma 3.3
-- given a system R returns a list permutations in dom(R) that have more than two normal forms under the system
confluence_counterexamples :: System -> [Perm]
confluence_counterexamples system = filter (not . same_test . map (normal_forms system) . try_apply system) domain_clusters 
  where 
    domain_clusters = sortOn length $ findSystemClusters system
    same_test xs = nub xs == [head xs]
    -- the O(R), R system, function in Ander's paper, the clusters of a systems domain
    findSystemClusters r = [c | p <- dom r, q <- dom r, c <- findClusters p q, not $ null c]

-- test whether a list of Int in actually a permutation
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

-- ovl function in our paper
ovl :: Perm -> Perm -> Int
ovl p q 
  | null $ findClusters p q = 0
  | otherwise = maximum $ map (\cluster -> (length p + length q) - length cluster) $ findClusters p q

-- check whether a rule is overlap invariant 
rule_check :: [Perm] -> Rule -> Bool
rule_check bigT (t, r) = ekat m t == ekat m r
  where 
    m = maximum $ map (ovl t) bigT

-- is system overlap invariant with respect to img(R)?
overlinvariance_check :: System -> Bool
overlinvariance_check system = all (rule_check image) system
  where
    image = filter ((==3) . length) $ img system

-- all of xs' consecutive sublists of length m
windows :: Int -> [a] -> [[a]]
windows m xs = [take m $ drop n xs | n <- [0..length xs - m]]

-- the sigma statistic in claesson's paper, parameterized by a single pattern
sigma :: Perm -> Perm -> Int
sigma perm pattern = sum $ zipWith zipper [1..] $ windows (length pattern) perm
  where 
    zipper i w = if standard w == pattern then i else 0

-- the sigma statistic introduced in this paper, parameterized by a set of patterns
sigma_sum :: Perm -> [Perm] -> Int
sigma_sum perm = sum . map (sigma perm)

-- the difference of sigma when applying the rule, not counting patterns that could cluster with the
-- left hand side of the rule
delta_of_rule :: [Perm] -> Rule -> Int
delta_of_rule patterns (t,r) = sigma_sum r patterns - sigma_sum t patterns

-- the algorithm we introduce in the paper, we assume that the system is terminating under
-- Sigma_img(R), f = Sigma_img(R)
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

-- give combos of elements in lists, fx. combos [[1,2],[3,4]] = [[1,3],[2,4],[1,4],[2,3]]
combos :: Ord a => [[a]] -> [[a]]
combos xss
  | _combos xss == [[]] = []
  | otherwise = _combos xss
  where
    _combos [] = [[]]
    _combos [[]] = [[]]
    _combos xs = if any (==[]) xs then [] else [a:b | a <- head xs, b <- _combos (tail xs)]

-- given a family of equivalences, often J in the paper, try to return a confluent and terminating system
make_system :: [Equivalence] -> Maybe System
make_system = make_confluent_system . filter overlinvariance_check . make_rewrite_systems 

-- generate all possible disjoint system given a family of equivalences
make_rewrite_systems :: [Equivalence] -> [System]
make_rewrite_systems = map concat . combos . map make_single_image_systems 
  where
    make_single_image_systems eq = [[(domain, image) | domain <- delete image eq] | image <- eq]

-- given a list of terminating systems, try to make them confluent and return the first success
make_confluent_system :: [System] -> Maybe System
make_confluent_system = listToMaybe . filter overlinvariance_check . sortOn length . mapMaybe (\sys -> confluentize (img sys) sys)

-- partitions of Sym_3, this ensures that all systems that can be generated from this are even
sym_partitions :: [[Equivalence]]
sym_partitions = tail $ map (filter (\p -> length p > 1)) $ partitions $ sym 3

-- all terminating and confluent systems we manage to generate, with the identity equivalence consed
-- to the front
trm_cfl_systems :: [([Equivalence], System)]
trm_cfl_systems = ([], []):(mapMaybe (\p -> if make_system p == Nothing then Nothing else Just (p, fromJust $ make_system p)) sym_partitions)

main :: IO ()
main = do
    -- keep information about clusters of the dom in a dictonary, ((r,s), O(r,s)), for maketex.sage
    let findSystemClustersDict sys = [((p, q), c) | p <- dom sys, q <- dom sys, c <- findClusters p q, not $ null c]

    -- output for maketex.sage
    mapM_ (\(p, sys) -> print (p, sys, dom sys, findSystemClustersDict sys)) trm_cfl_systems

