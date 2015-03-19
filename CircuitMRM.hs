{-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances -XNoMonomorphismRestriction -XDeriveFunctor -XKindSignatures -XDataKinds -XGADTs #-}

module CircuitMRM where

-- Fixpoint of List-of-Functors
data Fix (fs :: [* -> *]) where
  In :: Functor f => Elem f fs -> f (Fix fs) -> Fix fs

data Elem (f :: * -> *) (fs :: [* -> *]) where
  Here  :: Elem f (f ': fs)
  There :: Elem f fs -> Elem f (g ': fs)

class f :< fs where
  witness :: Elem f fs
instance f :< (f ': fs) where
  witness = Here
instance (f :< fs) => f :< (g ': fs) where
  witness = There witness

-- Smart fixpoint constructor
inn :: (f :< fs, Functor f) => f (Fix fs) -> Fix fs
inn = In witness

-- The Matches datatype
data Matches (fs :: [* -> *]) (a :: *) (b :: *) where
  Void  :: Matches '[] a b
  (:::) :: Functor f => (f a -> b) -> Matches fs a b -> Matches (f ': fs) a b

extractAt :: Elem f fs -> Matches fs a b -> (f a -> b)
extractAt Here        (f ::: _) = f
extractAt (There pos) (_ ::: fs) = extractAt pos fs

match :: Matches fs (Fix fs) b -> Fix fs -> b
match fs (In pos xs) = extractAt pos fs xs

-- Fold for List-of-Functors Datatypes
type Algebras fs a = Matches fs a a

fold :: Algebras fs a -> Fix fs -> a
fold ks (In pos xs) = extractAt pos ks (fmap (fold ks) xs)

-- Deep embedding
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

-- Smart construction 
type Circuit = Fix '[CircuitF]

identity :: (CircuitF :< fs) => Int -> Fix fs
identity = inn . Identity

fan :: (CircuitF :< fs) => Int -> Fix fs
fan = inn . Fan

above :: (CircuitF :< fs) => Fix fs -> Fix fs -> Fix fs
above x y = inn (Above x y)

beside :: (CircuitF :< fs) => Fix fs -> Fix fs -> Fix fs
beside x y = inn (Beside x y)

stretch :: (CircuitF :< fs) => [Int] -> Fix fs -> Fix fs
stretch xs x = inn (Stretch xs x)

-- Test
comp = widthAlg <+> wsAlg

eval :: Circuit -> Compose Width WellSized
eval = fold (comp ::: Void)

c1 = above (beside (fan 2) (fan 2)) 
           (above (stretch [2, 2] (fan 2))
                  (beside (identity 1) (beside (fan 2) (identity 1))))

test1 = gwidth $ eval c1
test2 = gwellSized $ eval c1

