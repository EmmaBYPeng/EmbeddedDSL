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

An alternative way to represent circuits is using folds as F-algebras~\cite{}. 
The shape of the circuit is given by functor |CircuitF| as follows:

> data CircuitF r = 
>     IdentityF Int
>  |  FanF Int
>  |  AboveF r r 
>  |  BesideF r r
>  |  StretchF [Int] r
>  deriving Functor

|CircuitF| abstracts the recursive occurrences of the datatype away, using a type
parameter r. We can then recover the datatype of Circuit, using a fixpoint:
\bruno{Why not use |Fix f|? How did Gibbons and Wu did it?}
\emma{They used this representation}

> data Circuit = In (CircuitF Circuit)

An algebra for CircuitF consists of a type a and a function taking a CircuitF 
of a-values to an a-value:

> type CircuitAlg a = CircuitF a -> a

Suppose we want to obtain the width of a circuit, we can pick {\em Width} as our 
evaluation target (i.e. the carrier type of {\em widthAlg}):

> type Width = Int
>
> widthAlg :: CircuitAlg Width
> widthAlg (IdentityF w)    = w
> widthAlg (FanF w)         = w
> widthAlg (AboveF x y)     = x
> widthAlg (BesideF x y)    = x + y
> widthAlg (StretchF xs x)  = sum xs

{\em widthAlg} here will give us the final evaluation result (i.e. the width) 
of a circuit, assuming all children of {\em AboveF}, {\em BesideF} and {\em StretchF} 
are already evaluated and are of type {\em Width}. 

Similarly, we can define {\em depthAlg} to obtain the depth of a circuit:

> type Depth = Int
>
> depthAlg :: CircuitAlg Depth
> depthAlg (IdentityF w)    = 0
> depthAlg (FanF w)         = 1
> depthAlg (AboveF x y)     = x + y
> depthAlg (BesideF x y)    = x `max` y
> depthAlg (StretchF xs x)  = x

Given a nested circuit, we need a fold to traverse the recursive 
data structure, using algebras defined earlier for evaluation at each recursive
step:

> fold :: CircuitAlg a -> Circuit -> a
> fold alg (In x) = alg (fmap (fold alg) x)

Each observation function for our circuit can be defined as a {\em fold}:

> width :: Circuit -> Width
> width = fold widthAlg

> depth :: Circuit -> Depth
> depth = fold depthAlg

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

Therefore, the parallel prefix circuit in Figure~\ref{fig:circuit2} can be 
constructed as:

> circuit1 = 
>   (fan 2 `beside` fan 2) `above`
>   stretch [2, 2] (fan 2) `above`
>   (identity 1 `beside` fan 2 `beside` identity 1)

It can be directly evaluated using observation functions defined earlier:

> test1 = width circuit1
> test2 = depth circuit1

