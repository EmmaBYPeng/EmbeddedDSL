module Repmin where

data Tree = Leaf Int | Branch Tree Tree

-- Traditional repMin: two traversals
minTree :: Tree -> Int
minTree (Leaf n) = n
minTree (Branch a b) = minTree a `min` minTree b

repTree :: Int -> Tree -> Tree
repTree k (Leaf n) = Leaf k
repTree k (Branch a b) = Branch (repTree k a) (repTree k b)

repMin :: Tree -> Tree
repMin t = repTree (minTree t) t

-- Circular programming
repMin' :: (Tree, Int) -> (Int, Tree)
repMin' (Leaf n, r) = (n, Leaf r)
repMin' (Branch a b, r) = (min1 `min` min2, Branch newTree1 newTree2)
  where (min1, newTree1) = repMin' (a, r)
        (min2, newTree2) = repMin' (b, r)

repMin2 tree = newTree
  where (min, newTree) = repMin' (tree, min)
