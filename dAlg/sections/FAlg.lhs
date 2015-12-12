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

> module FAlg where

> infixr <+>
>
> (<+>) :: (a :<: r, b :<: r) => GAlg r a -> GAlg r b -> GAlg r (Compose a b)
> (<+>) a1 a2 fa   = (a1 fa, a2 fa)

%endif

We represent the parallel prefix circuit using folds as F-algebras~\cite{}. 
The shape functor |CircuitF| is defined as:

> type Size = Int
>
> data CircuitF r = 
>     IdentityF Size
>  |  FanF Size
>  |  AboveF r r 
>  |  BesideF r r
>  |  StretchF [Size] r
>  deriving Functor

The algebraic datatype and corresponding constructors of circuits can be 
recovered as follows:

> data Circuit = In (CircuitF Circuit)
>
> identity :: Size -> Circuit
> identity = In . IdentityF
>
> fan :: Size -> Circuit
> fan = In . FanF
>
> above :: Circuit -> Circuit -> Circuit
> above x y = In (AboveF x y)
>
> beside :: Circuit -> Circuit -> Circuit
> beside x y = In (BesideF x y)
>
> stretch :: [Size] -> Circuit -> Circuit
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

> c1 = 
>   (fan 2 `beside` fan 2) `above`
>   stretch [2, 2] (fan 2) `above`
>   (identity 1 `beside` fan 2 `beside` identity 1)

As in section~\ref{sec:technique}, we define |type GAlg r a = CircuitF r -> a| as our
generic algebra type for |CircuitF|. Then we can define the fold as follows:

%if False

> type GAlg r a = CircuitF r -> a

%endif

> type CircuitAlg a  = GAlg a a
>
> fold :: CircuitAlg a -> Circuit -> a
> fold alg (In x) = alg (fmap (fold alg) x)

The type |CircuitAlg a| represents the fold-algebra of the circuit datatype.
Similar to the fold for arithmetic expressions, the fold here captures a recursive 
pattern, making interpretations for circuits compositional. 

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

\noindent Conventionally, for example, if we want to obtain the width of a circuit, 
we would define the algebra for width as:

> type Width' = Int
>
> widthAlg' :: CircuitAlg Width'
> widthAlg' (IdentityF w)    = w
> widthAlg' (FanF w)         = w
> widthAlg' (AboveF x y)     = x
> widthAlg' (BesideF x y)    = x + y
> widthAlg' (StretchF xs x)  = sum xs

This definition of |widthAlg'| is straightforward, but can not be reused modularly 
if later some other interpretations depend on it. It will cause the same problem as 
we discuss in section~\ref{sec:nonmodular} for arithmetic expressions. 
To allow for modularity, we use the following definition of |widthAlg| instead:

> newtype Width = Width {unwidth :: Size}
>
> widthAlg :: (Width :<: r) => GAlg r Width
> widthAlg (IdentityF w)    = Width w
> widthAlg (FanF w)         = Width w
> widthAlg (AboveF x y)     = Width (gwidth x)
> widthAlg (BesideF x y)    = Width (gwidth x + gwidth y)
> widthAlg (StretchF xs x)  = Width (sum xs)

Here we state that the output type |Width| of |GAlg| is a member of its input type 
|r| (i.e. |Width :<: r|), and use the helper function |gwidth| to retrieve the 
target value from values of type |r| (i.e. x and y):

> gwidth :: (Width :<: e) => e -> Size
> gwidth = unwidth . inter

The 'width' interpretation is simply:

> width :: Circuit -> Width
> width = fold widthAlg

\noindent In addition, we need the {\em newtype} wrapper here to allow other 
interpretations over the same underlying type. 
For instance, we can also have the 'depth' interpretation over integers:

> newtype Depth = Depth {undepth :: Size}
>
> depthAlg :: (Depth :<: r) => GAlg r Depth
> depthAlg (IdentityF w)     = Depth 0
> depthAlg (FanF w)          = Depth 1
> depthAlg (AboveF x y)      = Depth (gdepth x + gdepth y)
> depthAlg (BesideF x y)     = Depth (gdepth x `max` gdepth y)
> depthAlg (StretchF xs x)   = Depth (gdepth x)

Similarly, the output type |Depth| is a member of the input type of the algebra, 
and |gdepth| is used to retrieve values of target type |Depth|:

> gdepth :: (Depth :<: e) => e -> Size
> gdepth = undepth . inter

We can then define the 'depth' interpretation as:

> depth :: Circuit -> Depth
> depth = fold depthAlg

Though the above definition of algbras becomes sligtly more complicated compared 
with the traditional version, we show that it allows us to express multiple, dependent
and context-sensitive interpretations modularly while maintaining compositionality
in later sections.
