{-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances -XNoMonomorphismRestriction -XDeriveFunctor #-}

module CircuitF where

data CircuitF r = 
    Identity Int
  | Fan Int
  | Above r r 
  | Beside r r
  | Stretch [Int] r

newtype Width     = Width     {width :: Int}
newtype Depth     = Depth     {depth :: Int}
newtype WellSized = WellSized {wellSized :: Bool}

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

-- Fold
data Fix f = In {out :: f (Fix f)}

instance Functor CircuitF where
  fmap f (Identity w)   = Identity w
  fmap f (Fan w)        = Fan w
  fmap f (Above x y)    = Above (f x) (f y)
  fmap f (Beside x y)   = Beside (f x) (f y)
  fmap f (Stretch xs x) = Stretch xs (f x)

fold :: Functor f => (f a -> a) -> Fix f -> a
fold alg = alg . fmap (fold alg) . out

-- Test
comp = widthAlg <+> wsAlg

test1 = gwellSized $ fold comp c1 
test2 = gwidth $ fold comp c1
test3 = gdepth $ fold depthAlg c1

c1 :: Fix CircuitF
c1 = In (Above (In (Beside (In (Fan 2)) (In (Fan 2)))) 
               (In (Above (In (Stretch [2, 2] (In (Fan 2)))) 
                          (In (Beside (In (Identity 1)) 
                                      (In (Beside (In (Fan 2)) 
                                                  (In (Identity 1))))))))) 

