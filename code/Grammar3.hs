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

gfold :: Functor f => (t -> c) -> (([t]->[c]) -> c) -> (f c -> c) -> Pattern -> c
gfold v l f = trans . reveal where
  trans (Var x) = v x
  trans (Mu g)  = l (map (f . fmap trans) . g)

sfold :: (Eq t, Functor f) => (f t -> t) -> t -> Pattern -> t
sfold alg k = gfold id (head . fixVal (repeat k)) alg

-- Grammars -- New approach
data GrammarF v r = 
    Var v
  | Mu ([v] -> [GrammarF v r])
  | Term String 
  | E 
  | Seq r r 
  | Alt r r 
  deriving Functor

newtype PatternF r = Hide {reveal :: forall v. GrammarF v r}

data Pattern = In (PatternF Pattern)

type GAlg r a = PatternF r -> a

type PatternAlg a = GAlg a a

--foldG :: (PatternF a -> a) -> Pattern -> a
--foldG alg (In x) = alg (fmap (fold alg) x)

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



-- Evaluation
gAlg = nullF <+> firstF

{-
eval :: Pattern -> Compose Bool [String]
eval = sfold gAlg (False, [])

nullable :: Pattern -> Bool
nullable = inter . eval

firstSet :: Pattern -> [String]
firstSet = inter . eval

-- Example
g = Hide (Mu (\(~(a:_)) -> [Alt (Var a) (Term "x")]))

test1 = nullable g
test2 = firstSet g
-}

