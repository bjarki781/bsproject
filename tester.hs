import Data.Maybe
import Data.Char
import Data.List
import GHC.Exts
import System.IO

type Perm = [Int]
type Rule = (Perm, Perm)
type Equivalence = [Perm]

prm :: Int -> Perm
prm = map digitToInt . show

rule :: Int -> Int -> (Perm, Perm)
rule r s = (prm r, prm s)

sym :: Int -> [Perm]
sym n = permutations [1..n]

-- is there a nicer way?
partitions :: Ord a => [a] -> [[[a]]]
partitions xs = map tail $ par xs
    where par [] = [[[]]]
          par ys = nub $ map sort [b:p | b <- bites ys, p <- par (ys \\ b)]
          bites [] = [[]]
          bites ys = nub $ map sort $ [y:p | y <- ys, p <- []:(bites $ delete y ys)]

verify :: ([Equivalence], [Int]) -> Bool
verify (equivs, sequence) = test 6 equivs == (take 6 sequence)

main = do
    txt <- readFile "appendix.raw" 
    let ok = all (verify . read) $ lines txt

    putStrLn (if ok then "Test OK!" else "Test not OK!")

tester = map (\eqs -> (eqs, test 6 eqs)) $ map (filter (\p -> length p > 1)) $ partitions $ sym 3

test :: Int -> [Equivalence] -> [Int]
test n equivs = map (length . nubBy (relation equivs)) [ sym i | i <- [1..n]]

relation :: [Equivalence] -> (Perm -> Perm -> Bool)
relation equivs r s = elem s $ equivalence_class equivs r

equivalence_class :: [Equivalence] -> Perm -> [Perm]
equivalence_class equivs prm = until_static (>>= apply_rules rus) (apply_rules rus prm)
    where rus = concatMap (\e -> rules e []) equivs

-- repeat applying f to x f colllating the result in a pool until no new
-- elements are added
until_static :: Eq a => ([a] -> [a]) -> [a] -> [a]
until_static f x
    | nub ( f x `union` x) == x = x
    | otherwise = until_static f (x `union` f x)

-- all one way rules, antisymmetric
rules :: Equivalence -> [(Perm, Perm)] -> [(Perm, Perm)]
rules eq start = if null add then [] else add ++ rules eq add
    where add = [ (r,t) | r <- eq, t <- eq, (t,r) `notElem` start]
 
standard :: [Int] -> Perm
standard s = map (\e -> e - minimum s + 1) s
      
ekat :: Int -> [a] -> [a]
ekat n xs = drop (length xs - n) xs

lift :: Int -> Perm -> [Int]
lift n = map (+n)

apply_rule :: Rule -> Perm -> Int -> Perm
apply_rule (target, result) prm occ = take occ prm ++ lift (minimum prm_target - 1) result ++ drop (occ+length target) prm
    where prm_target = take (length target) $ drop occ prm

try_apply :: Rule -> Perm -> [Perm]
try_apply rule@(t,r) perm = [apply_rule rule perm i | i <- map fst $ occurrences t perm]

apply_rules :: [(Perm, Perm)] -> Perm -> [Perm]
apply_rules rus p = nub $ p:(concatMap (\rule -> try_apply rule p) rus)

-- rule replacement code follows; could be faster???

one_replace :: (Perm, Perm) -> Perm -> [Perm]
one_replace (t,r) perm = map (\(i, v) -> replace i (injection v) perm) (occurrences t perm)
    where injection v = let u = inverse r v in inverse u u

inverse :: (Ord a, Ord b) => [a] -> [b] -> [b]
inverse xs ys = map snd $ sort (zip xs (sort ys))

windows :: Int -> [a] -> [[a]]
windows m = foldr (zipWith (:)) (repeat []) . take m . tails

offset :: (Eq a, Num a) => [a] -> [a] -> Maybe a
offset xs ys =
  case nub (zipWith (-) xs ys) of
    [d] -> Just d
    _ -> Nothing

replace :: Int -> Perm -> Perm -> Perm
replace i v w = prefix ++ v ++ suffix
  where
    prefix = take i w
    suffix = drop (i + length v) w

occurrences :: (Eq a, Num a) => [a] -> [a] -> [(Int, [a])]
occurrences p xs =
  catMaybes $
  zipWith (\i v -> (i, v) <$ offset p v)
      [0..]
      (windows (length p) xs)


