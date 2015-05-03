{-# OPTIONS -XDeriveFunctor -XDeriveFoldable -XDeriveTraversable 
            -XExistentialQuantification -XRankNTypes #-}

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

-- Grammars -- Original approach
data PatternF a = Term String | E | Seq a a | Alt a a 
  deriving (Functor, Foldable, Traversable)

nullF :: PatternF Bool -> Bool
nullF (Term s)    = False
nullF E           = True
nullF (Seq g1 g2) = g1 && g2
nullF (Alt g1 g2) = g1 || g2

nullable = sfold nullF False

firstF :: PatternF (Bool,[String]) -> [String]
firstF (Term s) = [s]
firstF E = []
firstF (Seq (b1,a1) (_,a2)) = if b1 then union a1 a2 else a1
firstF (Alt (_,a1) (_,a2)) = union a1 a2

nullFirstF :: PatternF (Bool,[String]) -> (Bool,[String])
nullFirstF = compose (leftPart nullF) firstF

compose f g x = (f x, g x)

leftPart :: Functor f => (f a -> a) -> f (a, b) -> a
leftPart alg = alg . fmap fst

firstSet = sfold nullFirstF (False, [])


