{-# OPTIONS -XDeriveFunctor -XDeriveFoldable -XDeriveTraversable 
            -XExistentialQuantification -XRankNTypes -XTypeSynonymInstances 
            -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses 
            -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
            -XNoMonomorphismRestriction -XDeriveFunctor #-}

module Grammar where

import Data.Foldable
import Data.Traversable
import Data.List

-- Generic Graph
data Rec f a = 
    Var a 
  | Mu ([a] -> [f (Rec f a)])
  | In (f (Rec f a))

newtype Graph f = Hide {reveal :: forall a. Rec f a}

fix :: (a -> a) -> a
fix f = let r = f r in r -- f (fix f)

fixVal :: Eq a => a -> (a -> a) -> a
fixVal v f = if v == v' then v else fixVal v' f 
  where v' = f v

-- Generic Graph folds
gfold :: Functor f => (t -> c) -> (([t]->[c]) -> c) -> (f c -> c) -> Graph f -> c
gfold v l f = trans . reveal where
  trans (Var x) = v x
  trans (Mu g)  = l (map (f . fmap trans) . g)
  trans (In fa) = f (fmap trans fa)

sfold :: (Eq t, Functor f) => (f t -> t) -> t -> Graph f -> t
sfold alg k = gfold id (head . fixVal (repeat k)) alg

-- Grammars -- New approach
data PatternF a = Term String | E | Seq a a | Alt a a 
  deriving (Functor, Foldable, Traversable)

nullF :: (Bool :<: r) => PatternF r -> Bool
nullF (Term s)    = False
nullF E           = True
nullF (Seq g1 g2) = gNull g1 && gNull g2
nullF (Alt g1 g2) = gNull g1 || gNull g2

firstF :: (Bool :<: r, [String] :<: r) => PatternF r -> [String]
firstF (Term s)    = [s]
firstF E           = []
firstF (Seq g1 g2) = if gNull g1 then union (gFirst g1) (gFirst g2) else (gFirst g2)
firstF (Alt g1 g2) = union (gFirst g1) (gFirst g2)

-- Composition operator
type GAlg r a = PatternF r -> a

(<+>) :: (a :<: r, b :<: r) => GAlg r a -> GAlg r b -> GAlg r (Compose a b)
(<+>) a1 a2 (Term s)    = (a1 (Term s), a2 (Term s))
(<+>) a1 a2 E           = (a1 E, a2 E)
(<+>) a1 a2 (Seq g1 g2) = 
  (a1 (Seq (inter g1) (inter g2)), a2 (Seq (inter g1) (inter g2)))
(<+>) a1 a2 (Alt g1 g2) = 
  (a1 (Alt (inter g1) (inter g2)), a2 (Alt (inter g1) (inter g2)))

-- Type class
type Compose a b = (a, b)

class i :<: e where
  inter :: e -> i

instance i :<: i where
  inter = id

instance i :<: (Compose i i2) where
  inter = fst

instance (i :<: i2) => i :<: (Compose i1 i2) where
  inter = inter . snd

gNull :: (Bool :<: r) => r -> Bool
gNull = inter

gFirst :: ([String] :<: r) => r -> [String]
gFirst = inter

-- Evaluation
gAlg = nullF <+> firstF

eval :: Graph PatternF -> Compose Bool [String]
eval = sfold gAlg (False, [])

nullable :: Graph PatternF -> Bool
nullable = inter . eval

firstSet :: Graph PatternF -> [String]
firstSet = inter . eval

-- Example
g = Hide (Mu (\(~(a:_)) -> [Alt (Var a) (In (Term "x"))]))

test1 = nullable g
test2 = firstSet g

