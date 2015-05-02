{-# OPTIONS -XDeriveFunctor -XTypeSynonymInstances 
            -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses 
            -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
            -XNoMonomorphismRestriction -XDeriveFunctor #-}

module RepminNew where

data TreeF r = Leaf Int | Branch r r
  deriving Functor

data Tree = In (TreeF Tree)

newtype Replace = R {replace :: Int -> Tree}

minAlg :: (Int :<: r) => TreeF r -> Int
minAlg (Leaf n)     = n
minAlg (Branch x y) = gMin x `min` gMin y  

repTreeAlg :: (Replace :<: r) => TreeF r -> Replace
repTreeAlg (Leaf n)     = R (\k -> leaf k)
repTreeAlg (Branch a b) = R (\k -> branch (replace (gRep a) k) (replace (gRep b) k))

prettyAlg :: (String :<: r) => TreeF r -> String
prettyAlg (Leaf n)     = show n
prettyAlg (Branch x y) = gPretty x ++ " " ++ gPretty y

-- Type class
class i :<: e where
  inter :: e -> i

instance i :<: i where
  inter = id

instance i :<: (Compose i i2) where
  inter = fst

instance (i :<: i2) => i :<: (Compose i1 i2) where
  inter = inter . snd

gMin :: (Int :<: r) => r -> Int
gMin = inter

gRep :: (Replace :<: r) => r -> Replace
gRep = inter

gPretty :: (String :<: r) => r -> String
gPretty = inter

-- Composition operator
type GAlg r a = TreeF r -> a
type Compose i1 i2 = (i1, i2)

(<+>) :: (a :<: r, b :<: r) => GAlg r a -> GAlg r b -> GAlg r (Compose a b)
(<+>) a1 a2 (Leaf n)     = (a1 (Leaf n), a2 (Leaf n))
(<+>) a1 a2 (Branch x y) = 
  (a1 (Branch (inter x) (inter y)), a2 (Branch (inter x) (inter y)))

-- Smart constructors
leaf :: Int -> Tree
leaf = In . Leaf

branch :: Tree -> Tree -> Tree
branch a b = In (Branch a b) 
  
-- Fold
fold :: (TreeF a -> a) -> Tree -> a
fold alg (In x) = alg (fmap (fold alg) x)

-- Example Tree
t1 = branch (branch (leaf 8) (leaf 0)) (leaf 9)
compAlg1 = prettyAlg <+> (repTreeAlg <+> minAlg)

-- Evaluation
eval = fold compAlg1

minTree :: Tree -> Int
minTree = inter . eval

pretty :: Tree -> String
pretty = inter . eval

repTree :: Tree -> Tree
repTree t = replace r min
  where (r, min) = (inter (eval t)) :: (Compose Replace Int)

-- Test
test1 = minTree t1
test2 = pretty t1
test3 = pretty (repTree t1)
