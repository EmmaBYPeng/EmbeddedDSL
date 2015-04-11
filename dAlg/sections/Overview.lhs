%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{Existing Approaches}
\label{sec:overview}

To maintain the compositionality of an interpretation while bringing in dependencies,
Jeremy Gibbons proposed two approaches based on F-Algebra. 

%if False

> {-# OPTIONS
>  -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses
>  -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
>  -XNoMonomorphismRestriction -XDeriveFunctor -XExistentialQuantification
>  -XRankNTypes #-}

%endif

\subsection{Pairs for multiple interpretations with dependencies}
\label{sec:pair-for-composing-algebras}

While it is straightforward to add additional interpretaions that are independent 
of previously defined ones~\cite{Gibbons:14:Folding}, adding an interpretaion
that depends on 'secondary' interpretations of its parts can be tricky.

For example, whether a circuit is well formed or not depends on the widths of its
constituent parts. Since the interpretation is non-compositional
~\cite{Gibbons:14:Folding}, there is no corresponding {\em CircuitAlg}. To allow 
multiple interpretations with dependencies using algebras, 
Gibbons~\cite{Gibbons:14:Folding} proposed the following {\em zygomorphism}
~\cite{Fokkinga:90:Tupling}, making the semantic domain of the interpretaion 
(i.e. the carrier type of the algebra) a pair:

> type WellSized = Bool

> wswAlg :: CircuitAlg (WellSized, Width)
> wswAlg (IdentityF w)   = (True, w)
> wswAlg (FanF w)        = (True, w)
> wswAlg (AboveF x y)    = (fst x && fst y && snd x == snd y, snd x)
> wswAlg (BesideF x y)   = (fst x && fst y, snd x + snd y)
> wswAlg (StretchF ws x) = (fst x && length ws == snd x, sum ws)

In this way, {\em fold wswAlg} is still a fold, and individual interpretations can be
recovered as follows:

> wellSized1 :: Circuit -> WellSized
> wellSized1 x = fst (fold wswAlg x)

> width1 :: Circuit -> Width
> width1 x = snd (fold wswAlg x)

\subsection{Church encoding for multiple interpretations}
\label{sec:church-encoding}

From the previous section we can see that it is possible to provide dependent 
interpretaions by pairing semantics up and projecting the desired interpretation 
from the tuple. However, it is still clumsy and not modular: existing code needs 
to be revised every time a new interpretations is added. Moreover, for more than 
two interpretations, we have to either create a combination for each pair of 
interpretations, or use tuples which generally lack good language support.

Therefore, Gibbons~\cite{Gibbons:14:Folding} presented a single parametrized 
interpretation, which provides a universal generic interpretation as the 
{\em Church encoding}: 

> newtype Circuit1 = C1 {unC1 :: forall a. CircuitAlg a -> a}

> identity1 w   = C1 (\alg -> alg (IdentityF w))
> fan1 w        = C1 (\alg -> alg (FanF w))
> above1 x y    = C1 (\alg -> alg (AboveF (unC1 x alg) (unC1 y alg)))
> beside1 x y   = C1 (\alg -> alg (BesideF (unC1 x alg) (unC1 y alg)))
> stretch1 ws x = C1 (\alg -> alg (StretchF ws (unC1 x alg)))

It can then specialize to {\em width} and {\em depth}:

> width2 :: Circuit1 -> Width
> width2 x = unC1 x widthAlg

> depth2 :: Circuit1 -> Depth
> depth2 x = unC1 x depthAlg

However, one big problem with the above church encoding approach is that it does not 
support dependent interpretations. 


