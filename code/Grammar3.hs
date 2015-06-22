{-# OPTIONS -XDeriveFunctor -XDeriveFoldable -XDeriveTraversable 
            -XExistentialQuantification -XRankNTypes -XTypeSynonymInstances 
            -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses 
            -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
            -XNoMonomorphismRestriction -XDeriveFunctor #-}

module Grammar where

import Data.Foldable
import Data.Traversable
import Data.List

-- Generic Graph folds

fix :: (a -> a) -> a
fix f = let r = f r in r -- f (fix f)

fixVal :: Eq a => a -> (a -> a) -> a
fixVal v f = if v == v' then v else fixVal v' f 
  where v' = f v

sfold :: (Eq t) => (GrammarF t -> t) -> t -> Grammar -> t
sfold alg k (In p) = trans (reveal p) where
  trans (Var x)  = x
  trans (Mu g)   = (head . fixVal (repeat k)) (map trans . g)
  trans (Term s) = alg (Hide (Term s))
  trans (E)      = alg (Hide (E))
  trans (Alt g1 g2) = alg (fmap (sfold alg k) (Hide (Alt g1 g2)))  
  trans (Seq g1 g2) = alg (fmap (sfold alg k) (Hide (Seq g1 g2))) 

-- Grammars -- New approach
data PatternF v r = 
    Var v
  | Mu ([v] -> [PatternF v r])
  | Term String 
  | E 
  | Seq r r 
  | Alt r r 
  deriving Functor

newtype GrammarF r = Hide {reveal :: forall v. PatternF v r} deriving Functor

data Grammar = In (GrammarF Grammar)

type GAlg r a = GrammarF r -> a

nullF :: (Bool :<: r) => GAlg r Bool
nullF (Hide (Term s))     = False
nullF (Hide E)            = True
nullF (Hide (Seq g1 g2))  = gNull g1 && gNull g2
nullF (Hide (Alt g1 g2))  = gNull g1 || gNull g2

firstF :: (Bool :<: r, [String] :<: r) => GAlg r [String]
firstF (Hide (Term s))     = [s]
firstF (Hide E)            = []
firstF (Hide (Seq g1 g2))  = 
  if gNull g1 then union (gFirst g1) (gFirst g2) else (gFirst g2)
firstF (Hide (Alt g1 g2))  = union (gFirst g1) (gFirst g2)

(<+>) :: (a :<: r, b :<: r) => GAlg r a -> GAlg r b -> GAlg r (Compose a b)
(<+>) a1 a2 (Hide (Term s))     = (a1 (Hide (Term s)), a2 (Hide (Term s)))
(<+>) a1 a2 (Hide E)            = (a1 (Hide E), a2 (Hide E))
(<+>) a1 a2 (Hide (Seq g1 g2))  = 
  (a1 (Hide (Seq (inter g1) (inter g2))), a2 (Hide (Seq (inter g1) (inter g2))))
(<+>) a1 a2 (Hide (Alt g1 g2))  = 
  (a1 (Hide (Alt (inter g1) (inter g2))), a2 (Hide (Alt (inter g1) (inter g2))))


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

-- Smart constructors
--var :: GrammarF v r -> Pattern
--var v = In (Hide (Var v))

term x = In (Hide (Term x))
empty = In (Hide E)
alt x y = In (Hide (Alt x y))
seq x y = In (Hide (Seq x y))

-- Evaluation
gAlg = nullF <+> firstF

eval :: Grammar -> Compose Bool [String]
eval = sfold gAlg (False, [])

nullable :: Grammar -> Bool
nullable = inter . eval

firstSet :: Grammar -> [String]
firstSet = inter . eval

-- Example
--g1 = Hide (Mu (\(~(a:_)) -> [Alt (Var a) (Term "x")]))

g = term "x"

test1 = nullable empty 
test2 = firstSet g

