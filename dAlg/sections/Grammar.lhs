%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{Application: Grammars}
\label{sec:case_study}

This section shows how our technique can be applied to grammar analysis and 
transformations. We present nullability and first set operations on grammars with
recursive multi-binders.

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


> type Compose i1 i2 = (i1, i2)

> class i :<: e where
>   inter :: e -> i

> instance i :<: i where
>   inter = id

> instance i :<: (Compose i i2) where
>   inter = fst

> instance (i :<: i2) => i :<: (Compose i1 i2) where
>   inter = inter . snd

> infixr <+>
>
> (<+>) :: (a :<: r, b :<: r) => GAlg r a -> GAlg r b -> GAlg r (Compose a b)
> (<+>) a1 a2 fa = (a1 fa, a2 fa)

> fix :: (a -> a) -> a
> fix f = let r = f r in r 

> fixVal :: Eq a => a -> (a -> a) -> a
> fixVal v f = if v == v' then v else fixVal v' f 
>   where v' = f v

> sfold :: (Eq t) => (GrammarF t -> t) -> t -> Grammar -> t
> sfold alg k (In p) = trans (reveal p) where
>   trans (Var x)      = x
>   trans (Mu g)       = (head . fixVal (repeat k)) (map trans . g)
>   trans (Term s)     = alg (Hide (Term s))
>   trans (E)          = alg (Hide (E))
>   trans (Alt g1 g2)  = alg (fmap (sfold alg k) (Hide (Alt g1 g2)))  
>   trans (Seq g1 g2)  = alg (fmap (sfold alg k) (Hide (Seq g1 g2)))

%endif

\subsection{Grammars}
\label{sec:grammar}

A grammar is a group of mutually recursive productions, each associated with a name 
and a pattern. Each pattern belongs to one of the followings: a termimal, the empty 
string, a sequence of two patterns, or an alternative of two patterns. As a mutually 
recursive collection of patterns where patterns can refer to themselves or other 
patterns~\cite{oliveira12}, the grammar datatype is defined as follows: 

> data PGrammar v r = Var v | Mu ([v] -> [PGrammar v r]) | Term String | E | Seq r r | Alt r r
>   deriving Functor
>
> newtype GrammarF r = Hide {reveal :: forall v. PGrammar v r} deriving Functor
>
> data Grammar = In (GrammarF Grammar)

Here binders are represented by Parmetric Higher-Order Syntax (PHOAS)
~\cite{chlipala08}, which include the variable case and recursive multi-binders. 
For example, a left-recursive grammar can be constructed as: 

~\emma{Our definition of grammar datatype here will cause trouble constructing 
grammars. In the following example, 'a' on the LHS is not in scope on the RHS 
inside 'Seq', type check fail. However, another definition of the grammar datatype
avoids this problem, but it does not work with |:<:| in algebra definitions 
(see EmbeddedDSL/code/GrammarNew.hs). Generic definition that separately define
binders and pattern works for both problems (see EmbeddedDSL/code/Grammar2.hs)}

> g = In (Hide (Mu (\(~(a:_)) -> [Seq (In (Hide (Var a))) (In (Hide E))])))

The first operation on grammars is nullability analysis. It checks if a given grammar
can produce the empty string. Terms are not nullable, the empty string is nullable, 
while the nullabilities for sequences and alternatives depend on the nullabilities of 
their constituent patterns:

> type GAlg r a = GrammarF r -> a
>
> nullF :: (Bool :<: r) => GAlg r Bool
> nullF (Hide (Term s))     = False
> nullF (Hide E)            = True
> nullF (Hide (Seq g1 g2))  = gNull g1 && gNull g2
> nullF (Hide (Alt g1 g2))  = gNull g1 || gNull g2

Another operation is the first set analysis. The first set for a pattern is the set
of terminals that begin the strings derived from the pattern. For a sequence of 
patterns, its first set is the union of first sets of its two constituent patterns 
only when the first patttern is nullable. Although the interpretation for first 
set analysis depends on the interpretation for nullability, we can define its algebra 
independently as follows: 

> firstF :: (Bool :<: r, [String] :<: r) => GAlg r [String]
> firstF (Hide (Term s))     = [s]
> firstF (Hide E)            = []
> firstF (Hide (Seq g1 g2))  = 
>   if gNull g1 then union (gFirst g1) (gFirst g2) else (gFirst g2)
> firstF (Hide (Alt g1 g2))  = union (gFirst g1) (gFirst g2)
  
Helper functions |gNull| and |gFirst| help us retrieve values of target types from 
values of composed types:
 
> gNull :: (Bool :<: r) => r -> Bool
> gNull = inter
>
> gFirst :: ([String] :<: r) => r -> [String]
> gFirst = inter

Using the same composition operator |<+>|, we can compose algebras together the old 
way:

> compAlg = nullF <+> firstF

While how we define algbras and the composition operator remains unchanged, 
the definition for fold has changed to accomodate a starting value of type t, 
which gives us |sfold| (Detailed elaboration of |sfold| is omitted here as it is not 
of the primary concern of this paper)~\cite{oliveira12}: 

< sfold :: (Eq t) => (GrammarF t -> t) -> t -> Grammar -> t

$False$ serves as the starting value for nullability analysis and the empty set |[]| 
for first set analysis. The compositional evaluation function takes the composed
algebra as well as the pair of starting values:

> eval :: Grammar -> Compose Bool [String]
> eval = sfold compAlg (False, [])

Individual interpretations, namely, |nullable| and |firstSet|, can be retrieved as
follows:

> nullable :: Grammar -> Bool
> nullable = inter . eval
>
> firstSet :: Grammar -> [String]
> firstSet = inter . eval

%if False

> term x   = In (Hide (Term x))
> empty    = In (Hide E)
> alt x y  = In (Hide (Alt x y))
> seq x y  = In (Hide (Seq x y))

> g1 = alt empty (term "x")
> test1 = nullable g1

> g2 = In (Hide (Mu (\(~(a:_)) -> [Var a])))
> test2 = nullable g2

%endif

Our approach works perfectly with the grammar example by providing mudular and
compositional interpretations for grammar analysis. In particular, it works well 
with binders, which is not mentioned in Gibbon and Wu's work~\cite{gibbons14}. 


