{-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances -XNoMonomorphismRestriction -XDeriveFunctor -XKindSignatures -XDataKinds -XGADTs #-}

module CircuitMRM_base where

data CircuitFB r = 
    Identity Int
  | Fan Int
  | Beside r r
  deriving Functor

newtype Width     = Width     {width :: Int}
newtype WellSized = WellSized {wellSized :: Bool}

-- F-Algebra
widthAlg :: CircuitFB Width -> Width
widthAlg (Identity w)   = Width w
widthAlg (Fan w)        = Width w
widthAlg (Beside x y)   = Width (width x + width y)

wsAlg :: CircuitFB WellSized -> WellSized
wsAlg (Identity w)   = WellSized True
wsAlg (Fan w)        = WellSized True
wsAlg (Beside x y)   = WellSized (wellSized x && wellSized y)

-- Fold
data Fix f = In {out :: f (Fix f)}

fold :: Functor f => (f a -> a) -> Fix f -> a
fold alg = alg . fmap (fold alg) . out

-- Smart Constructors
identity :: Int -> Fix CircuitFB
identity = In . Identity

fan :: Int -> Fix CircuitFB
fan = In . Fan

beside :: Fix CircuitFB -> Fix CircuitFB -> Fix CircuitFB
beside x y = In (Beside x y)

-- Test
c1 = beside (fan 2) (identity 2)

test1 = wellSized $ fold wsAlg c1
test2 = width $ fold widthAlg c1

