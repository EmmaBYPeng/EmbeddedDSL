%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{Application: Grammars}
\label{sec:grammar}

This section shows a concrete example with grammar analysis and transformations.

%if False

> {-# OPTIONS -XDeriveFunctor -XDeriveFoldable -XDeriveTraversable 
>             -XExistentialQuantification -XRankNTypes -XTypeSynonymInstances 
>             -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses 
>             -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
>             -XNoMonomorphismRestriction -XDeriveFunctor #-}

> module Grammar where

> import Data.Foldable
> import Data.Traversable
> import Data.List


> infixr 6 <+>

> (<+>) :: (a :<: r, b :<: r) => PatternAlg r a -> PatternAlg r b ->
>                                PatternAlg r (Compose a b)
> (<+>) a1 a2 fa   = (a1 fa, a2 fa)

> type Compose i1 i2 = (i1, i2)

> class i :<: e where
>   inter :: e -> i

> instance i :<: i where
>   inter = id

> instance i :<: (Compose i i2) where
>   inter = fst

> instance (i :<: i2) => i :<: (Compose i1 i2) where
>   inter = inter . snd

> fix :: (a -> a) -> a
> fix f = let r = f r in r 

> fixVal :: Eq a => a -> (a -> a) -> a
> fixVal v f = if v == v' then v else fixVal v' f 
>   where v' = f v

> gfold :: Functor f => (t -> c) -> (([t]->[c]) -> c) -> (f c -> c) -> Graph f -> c
> gfold v l f = trans . reveal where
>   trans (Var x) = v x
>   trans (Mu g)  = l (map (f . fmap trans) . g)
>   trans (In fa) = f (fmap trans fa)

> sfold :: (Eq t, Functor f) => (f t -> t) -> t -> Graph f -> t
> sfold alg k = gfold id (head . fixVal (repeat k)) alg

%endif

> data Rec f a = 
>     Var a 
>   | Mu ([a] -> [f (Rec f a)])
>   | In (f (Rec f a))

> newtype Graph f = Hide {reveal :: forall a. Rec f a}

> data PatternF a = Term String | E | Seq a a | Alt a a 
>   deriving (Functor, Foldable, Traversable)

> type PatternAlg r a = PatternF r -> a

> nullF :: (Bool :<: r) => PatternAlg r Bool
> nullF (Term s)     = False
> nullF E            = True
> nullF (Seq g1 g2)  = gNull g1 && gNull g2
> nullF (Alt g1 g2)  = gNull g1 || gNull g2

> firstF :: (Bool :<: r, [String] :<: r) => PatternAlg r [String]
> firstF (Term s)     = [s]
> firstF E            = []
> firstF (Seq g1 g2)  = if gNull g1 then union (gFirst g1) (gFirst g2) else (gFirst g2)
> firstF (Alt g1 g2)  = union (gFirst g1) (gFirst g2)

  
> gNull :: (Bool :<: r) => r -> Bool
> gNull = inter

> gFirst :: ([String] :<: r) => r -> [String]
> gFirst = inter

> compAlg = nullF <+> firstF

> eval :: Graph PatternF -> Compose Bool [String]
> eval = sfold compAlg (False, [])

> nullable :: Graph PatternF -> Bool
> nullable = inter . eval

> firstSet :: Graph PatternF -> [String]
> firstSet = inter . eval

> g = Hide (Mu (\(~(a:_)) -> [Alt (Var a) (In (Term "x"))]))

> test1 = nullable g
> test2 = firstSet g



