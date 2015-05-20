{-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances -XNoMonomorphismRestriction -XDeriveFunctor #-}

module CircuitF where

-- Deep embedding?
data CircuitF r = 
    Identity Int
  | Fan Int
  | Above r r 
  | Beside r r
  | Stretch [Int] r
  deriving Functor

newtype Width     = Width     {width :: Int}
newtype Depth     = Depth     {depth :: Int}
newtype WellSized = WellSized {wellSized :: Bool}
newtype Layout    = Layout    {layout :: (Int -> Int) -> [[(Int, Int)]]}

-- F-Algebra
widthAlg :: (Width :<: r) => CircuitF r -> Width
widthAlg (Identity w)   = Width w
widthAlg (Fan w)        = Width w
widthAlg (Above x y)    = Width (gwidth x)
widthAlg (Beside x y)   = Width (gwidth x + gwidth y)
widthAlg (Stretch xs x) = Width (sum xs)

depthAlg :: (Depth :<: r) => CircuitF r -> Depth
depthAlg (Identity w)   = Depth 0
depthAlg (Fan w)        = Depth 1
depthAlg (Above x y)    = Depth (gdepth x + gdepth y)
depthAlg (Beside x y)   = Depth (gdepth x `max` gdepth y)
depthAlg (Stretch xs x) = Depth (gdepth x)

wsAlg :: (WellSized :<: r, Width :<: r) => CircuitF r -> WellSized
wsAlg (Identity w)   = WellSized True
wsAlg (Fan w)        = WellSized True
wsAlg (Above x y)    = WellSized (gwellSized x && gwellSized y && 
                                  gwidth x == gwidth y)
wsAlg (Beside x y)   = WellSized (gwellSized x && gwellSized y)
wsAlg (Stretch xs x) = WellSized (gwellSized x && length xs == gwidth x)

layoutAlg :: (Width :<: r, Layout :<: r) => CircuitF r -> Layout
layoutAlg (Identity w)   = Layout (\f -> [])
layoutAlg (Fan w)        = Layout (\f -> [[(f 0, f i) | i <- [1..w-1]]])
layoutAlg (Above x y)    = Layout (\f -> (glayout x f ++ glayout y f))
layoutAlg (Beside x y)   =  
    Layout (\f -> lzw (++) (glayout x f) (glayout y (((gwidth x)+) . f)))
layoutAlg (Stretch xs x) = 
    Layout (\f -> glayout x (pred . ((scanl1 (+) xs)!!) . f))

lzw :: (a -> a -> a) -> [a] -> [a] -> [a]
lzw f [] ys         = ys
lzw f xs []         = xs
lzw f (x:xs) (y:ys) = f x y : lzw f xs ys

-- Compose two algebras
type GAlg r a = CircuitF r -> a
type Compose i1 i2 = (i1, i2)

(<+>) :: (a :<: r, b :<: r) => GAlg r a -> GAlg r b -> GAlg r (Compose a b)
(<+>) a1 a2 (Identity w)   = (a1 (Identity w), a2 (Identity w))
(<+>) a1 a2 (Fan w)        = (a1 (Fan w), a2 (Fan w))
(<+>) a1 a2 (Above x y)    = (a1 (Above (inter x) (inter y)) 
                              , a2 (Above (inter x) (inter y)))
(<+>) a1 a2 (Beside x y)   = (a1 (Beside (inter x) (inter y)) 
                              , a2 (Beside (inter x) (inter y)))
(<+>) a1 a2 (Stretch xs x) = (a1 (Stretch xs (inter x)), a2 (Stretch xs (inter x)))

-- Type class
class i :<: e where
  inter :: e -> i

instance i :<: i where
  inter = id

instance i :<: (Compose i i2) where
  inter = fst

instance (i :<: i2) => i :<: (Compose i1 i2) where
  inter = inter . snd
 
gwidth :: (Width :<: e) => e -> Int
gwidth = width . inter

gdepth :: (Depth :<: e) => e -> Int
gdepth = depth . inter

gwellSized :: (WellSized :<: e) => e -> Bool 
gwellSized = wellSized . inter

glayout :: (Layout :<: e) => e -> ((Int -> Int) -> [[(Int, Int)]])
glayout = layout . inter

-- Fold and smart constructors
data Fix f = In {out :: f (Fix f)}

fold :: Functor f => (f a -> a) -> Fix f -> a
fold alg = alg . fmap (fold alg) . out

identity :: Int -> Fix CircuitF
identity = In . Identity

fan :: Int -> Fix CircuitF
fan = In . Fan

above :: Fix CircuitF -> Fix CircuitF -> Fix CircuitF
above x y = In (Above x y)

beside :: Fix CircuitF -> Fix CircuitF -> Fix CircuitF
beside x y = In (Beside x y)

stretch :: [Int] -> Fix CircuitF -> Fix CircuitF
stretch xs x = In (Stretch xs x)

-- Test
comp = depthAlg <+> (layoutAlg <+> (widthAlg <+> wsAlg))

c1 = above (beside (fan 2) (fan 2)) 
           (above (stretch [2, 2] (fan 2))
                  (beside (identity 1) (beside (fan 2) (identity 1)))) 

test1 = gwellSized $ fold comp c1 
test2 = gwidth $ fold comp c1
test3 = gdepth $ fold comp c1
test4 = (glayout $ fold comp c1) id
