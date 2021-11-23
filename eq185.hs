import PRS (Perm, numberOfEquivalenceClasses)
import Data.List

-- 132 ≡ 312
eq32 :: [[Perm]]
eq32 = [[[1,3,2],[3,1,2]]]

-- 132 ≡ 312
-- 213 ≡ 321
eq50 :: [[Perm]]
eq50 = [[[1,3,2],[3,1,2]],
        [[2,1,3],[3,2,1]]
       ]

-- 231 ≡ 312 ≡ 321
eq97 :: [[Perm]]
eq97 = [[[2,3,1],[3,1,2],[3,2,1]]]

-- 123 ≡ 132
-- 231 ≡ 312 ≡ 321
eq108 :: [[Perm]]
eq108 = [[[1,2,3],[1,3,2]],
         [[2,3,1],[3,1,2],[3,2,1]]
        ]

-- 132 ≡ 231 ≡ 312
-- 213 ≡ 321
eq109 :: [[Perm]]
eq109 = [[[1,3,2],[2,3,1],[3,1,2]],
         [[2,1,3],[3,2,1]]
        ]

-- 123 ≡ 213 ≡ 321
-- 132 ≡ 231 ≡ 312
eq185 :: [[Perm]]
eq185 = [[[1,2,3],[2,1,3],[3,2,1]],
         [[1,3,2],[2,3,1],[3,1,2]]
        ]

partitions :: Ord a => [a] -> [[[a]]]
partitions xs = map tail $ par xs
    where par [] = [[[]]]
          par ys = nub $ map sort [b:p | b <- bites ys, p <- par (ys \\ b)]
          bites [] = [[]]
          bites ys = nub $ map sort $ [y:p | y <- ys, p <- []:(bites $ delete y ys)]

sym :: Int -> [Perm]
sym n = permutations [1..n]

tester = map (\eqs -> (eqs, take 7 $ drop 1 $ numberOfEquivalenceClasses eqs)) $ map (filter (\p -> length p > 1)) $ partitions $ sym 3

main :: IO ()
main =
  mapM_ print tester
    

