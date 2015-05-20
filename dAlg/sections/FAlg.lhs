%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt


\subsection{Circuits using Folds and F-Algebras}
\label{sec:f-algebra}

%if False

> {-# OPTIONS
>  -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses
>  -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
>  -XNoMonomorphismRestriction -XDeriveFunctor -XExistentialQuantification
>  -XRankNTypes #-}

%endif

We represent the parallel prefix circuit using folds as F-algebras~\cite{}. 
The shape functor |CircuitF| is defined as:

> data CircuitF r = 
>     IdentityF Int
>  |  FanF Int
>  |  AboveF r r 
>  |  BesideF r r
>  |  StretchF [Int] r
>  deriving Functor

The algebraic datatype and corresponding constructors of the circuit can be 
recovered as follows:
\bruno{Why not use |Fix f|? How did Gibbons and Wu did it?}
\emma{They used this representation}

> data Circuit = In (CircuitF Circuit)

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

The first primitive is {\em identity}. An {\em identity} of width n generates n 
parallel wires. For the other premitive {\em fan}, it takes n inputs, and combines 
the first one with each of the rest using the binary operator |.|. 
To vertically combine two circuits of the same width, 
{\em above} places the first input circuit on top of the second one. On the other 
hand, {\em beside} combines two circuits horizontally, with no restriction on the
widths of its input circuits. Lastly, we can stretch out a circuit according to a 
list of widths {\em ws} = [$w_1$, $w_2$, ..., $w_k$] using the {\em stretch}
constructor. While keeping the original flow of operations 
(i.e. the position of nodes and diagonal wires that connect different nodes), 
$w_i$ parallel wires are added on the left of the $i^{th}$ input wire for $i$ from 1 
to $k$, resulting in a circuit of width {\em sum ws}. 

\noindent We can construct the parallel prefix circuit in Figure~\ref{fig:circuit2} 
as:

> circuit1 = 
>   (fan 2 `beside` fan 2) `above`
>   stretch [2, 2] (fan 2) `above`
>   (identity 1 `beside` fan 2 `beside` identity 1)

The generic algebra type and fold for |CircuitF| are defined as:

> type GAlg r a = CircuitF r -> a
> type CircuitAlg a = GAlg a a

> fold :: CircuitAlg a -> Circuit -> a
> fold alg (In x) = alg (fmap (fold alg) x)

%if False

> type Compose i1 i2 = (i1, i2)

> class i :<: e where
>   inter :: e -> i

> instance i :<: i where
>   inter = id

> instance i :<: (Compose i i2) where
>   inter = fst

> instance (i :<: i2) => i :<: (Compose i1 i2) where
>   inter = inter . snd

%endif

\noindent For example, if we want to obtain the width of a circuit, 
we can define the algebra for width as follows:

> newtype Width = Width {unwidth :: Int}
>
> widthAlg :: (Width :<: r) => GAlg r Width
> widthAlg (IdentityF w)   = Width w
> widthAlg (FanF w)        = Width w
> widthAlg (AboveF x y)    = Width (gwidth x)
> widthAlg (BesideF x y)   = Width (gwidth x + gwidth y)
> widthAlg (StretchF xs x) = Width (sum xs)

> width :: Circuit -> Width
> width = fold widthAlg

Similarly, we can define {\em depthAlg} to obtain the depth of a circuit:

> newtype Depth = Depth {undepth :: Int}
>
> depthAlg :: (Depth :<: r) => GAlg r Depth
> depthAlg (IdentityF w)    = Depth 0
> depthAlg (FanF w)         = Depth 1
> depthAlg (AboveF x y)     = Depth (gdepth x + gdepth y)
> depthAlg (BesideF x y)    = Depth (gdepth x `max` gdepth y)
> depthAlg (StretchF xs x)  = Depth (gdepth x)

> depth :: Circuit -> Depth
> depth = fold depthAlg

The {\em newtype} wrapper is needed here to allow multiple interpretations over the 
same underlying type. Helper functions |gwidth| and |gdepth| are defined as:

> gwidth :: (Width :<: e) => e -> Int
> gwidth = unwidth . inter

> gdepth :: (Depth :<: e) => e -> Int
> gdepth = undepth . inter
