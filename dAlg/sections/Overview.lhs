%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{An Overview of Existing Approaches}
\label{sec:overview}

%if False

> {-# OPTIONS
>  -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses
>  -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
>  -XNoMonomorphismRestriction -XDeriveFunctor -XExistentialQuantification
>  -XRankNTypes #-}

%endif

\subsection{Scans}
\label{sec:scan}


\subsection{F-Algebras}
\label{sec:f-algebra}

The circuit mentioned above can be constructed using F-Algebras. 
The shape of the circuit is given by functor {\em CircuitF} as follows, 
where r marks the recursive spots:

> data CircuitF r = 
>    IdentityF Int
>  | FanF Int
>  | AboveF r r 
>  | BesideF r r
>  | StretchF [Int] r
>  deriving Functor

We can recover the Circuit datatype from its shape functor {\em CircuitF}:
> data Circuit = In (CircuitF Circuit)

An algebra for a functor f consists of a type a and a function taking an f-structure 
of a-values to an a-value. For {\em CircuitF}, this is:
> type CircuitAlg a = CircuitF a -> a

Suppose we want to obtain the width of a circuit, we can pick {\em Width} as our 
evaluation target, which is also the carrier type of the algebra {\em widthAlg}:

> type Width = Int

> widthAlg :: CircuitAlg Width
> widthAlg (IdentityF w)   = w
> widthAlg (FanF w)        = w
> widthAlg (AboveF x y)    = x
> widthAlg (BesideF x y)   = x + y
> widthAlg (StretchF xs x) = sum xs

{\em widthAlg} here will give us the final evaluation result of a circuit, 
assuming all children of {\em AboveF}, {\em BesideF} and {\em StretchF} 
are already evaluated and are of type {\em Width}. 

Similarly, we can define {\em depthAlg} to get the depth of a circuit:

> type Depth = Int

> depthAlg :: CircuitAlg Depth
> depthAlg (IdentityF w)   = 0
> depthAlg (FanF w)        = 1
> depthAlg (AboveF x y)    = x + y
> depthAlg (BesideF x y)   = x `max` y
> depthAlg (StretchF xs x) = x

Given a nested circuit, we also need to define a fold to traverse the recursive 
data structure, using the algebra defined earlier for evaluation at each step:

> fold :: CircuitAlg a -> Circuit -> a
> fold alg (In x) = alg (fmap (fold alg) x)

Now a compositional observation function for our circuit can be defined as:

> width :: Circuit -> Width
> width = fold widthAlg

In order to conveniently construct circuits with {\em CircuitF}, we define the 
following smart constructos: 

> identity :: Int -> Circuit
> identity = In . IdentityF

> fan :: Int -> Circuit
> fan = In . FanF

> above :: Circuit -> Circuit -> Circuit
> above x y = In (AboveF x y)

> beside :: Circuit -> Circuit -> Circuit
> beside x y = In (BesideF x y)

> stretch :: [Int] -> Circuit -> Circuit
> stretch xs x = In (StretchF xs x)

Therefore, the Brent-Kung parallel prefix circuit in Figure 1 can be constructed as:
> circuit1 = above (beside (fan 2) (fan 2)) 
>                  (above (stretch [2, 2] (fan 2))
>                         (beside (identity 1) (beside (fan 2) (identity 1))))

\subsection{Pairs for multiple interpretations with dependencies}
\label{sec:pair-for-composing-algebras}

While it is straight forward to add additional interpretaions that are independent 
of the previously defined ones~\cite{Gibbons:14:Folding}, adding an interpretaion
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

Individual interpretations can then be recovered as follows:

> wellSized1 :: Circuit -> WellSized
> wellSized1 x = fst (fold wswAlg x)

> width1 :: Circuit -> Width
> width1 x = snd (fold wswAlg x)

\subsection{Church encoding for multiple interpretations}
\label{sec:church-encoding}

From the previous section we can see that it is possible to provide multiple 
interpretaions by pairing semantics up and projecting the desired interpretation 
from the tuple. However, it is still clumsy and not modular: existing code needs 
to be revised every time a new interpretations is added. Moreover, for more than 
two interpretations, we have to either create combinations for each pair of 
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

Then it can specialize to {\em width} and {\em depth}:

> width2 :: Circuit1 -> Width
> width2 x = unC1 x widthAlg

> depth2 :: Circuit1 -> Depth
> depth2 x = unC1 x depthAlg

However, one big problem with the above church encoding approach is that it does not 
support dependent interpretations. 


