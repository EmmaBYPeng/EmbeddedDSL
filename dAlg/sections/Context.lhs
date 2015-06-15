%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\subsection{Context-sensitive Interpretations}
\label{sec:context}

%if False

> {-# OPTIONS
>  -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses
>  -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
>  -XNoMonomorphismRestriction -XDeriveFunctor #-}

> module Context where

> import FAlg
> import DependentAlg 

%endif

Connections between vertical wires of a circuit can be modeled by dividing the circuit
into different layers, with local connections only go rightwards from one layer to 
the next. For instance, connections of the circuit shown in Figure~\ref{fig:circuit2}
can be represented as:

< [[(0,1), (2,3)], [(1,3)], [(1,2)]]

The above shows that the circuit has 3 layers. The first layer has connections from
the first wire to the second, and from the second to the third. The second layer has
only one connection from the first wire to the third one, while the third layer has
a connection from the first wire to the second. 

\noindent Gibbons and Wu modeled such layering layout of a circuit using the 
following context-sensitive interpretation:

> type Layout' = [[(Size, Size)]]
>
> tlwAlg :: CircuitAlg ((Size -> Size) -> Layout', Width')
> tlwAlg (IdentityF w)    = (\f -> [], w)
> tlwAlg (FanF w)         = (\f -> [[(f 0, f i) | i <- [1..w-1]]], w)
> tlwAlg (AboveF x y)     = (\f -> fst x f ++ fst y f, snd x)
> tlwAlg (BesideF x y)    = (\f -> lzw (++) (fst x f) (fst y ((snd x +) . f)), snd x + snd y)
> tlwAlg (StretchF ws x)  = (\f -> fst x (pred . (vs!!) . f), sum ws) 
>   where vs = scanl1 (+) ws 

The |f| in |tlwAlg| is an accumulating parameter, which in this case, represents a 
transformation on wire indices.
The function $lzw$ stands for "long zip with"~\cite{gibbons98}, which, as 
Gibbons and Wu pointed out: 
\say{... zips two lists together and returns a result as long as the longer argument.}

> lzw :: (a -> a -> a) -> [a] -> [a] -> [a]
> lzw f' [] ys         = ys
> lzw f' xs []         = xs
> lzw f' (x:xs) (y:ys) = f' x y : lzw f' xs ys

Since the layout of a circuit depends on the widths of its constituent parts, the 
interpretation for layout is dependent and needs to be paired up with the 
interpretation of width to maintain compositionality.  

Instead of modeling only the connections between wires, we make the whole
transformation as a newtype called $Layout$:

> newtype Layout = Layout {unlayout :: (Size -> Size) -> [[(Size, Size)]]}
>
> layoutAlg :: (Width :<: r, Layout :<: r) => GAlg r Layout
> layoutAlg (IdentityF w)    = Layout (\f -> [])
> layoutAlg (FanF w)         = Layout (\f -> [[(f 0, f i) | i <- [1..w-1]]])
> layoutAlg (AboveF x y)     = Layout (\f -> (glayout x f ++ glayout y f))
> layoutAlg (BesideF x y)    = Layout (\f -> lzw (++) (glayout x f) (glayout y (((gwidth x)+) . f)))
> layoutAlg (StretchF xs x)  = Layout (\f -> glayout x (pred . ((scanl1 (+) xs)!!) . f))

With our technique, instead of |fst| and |snd|, helper functions |glayout| and 
|gwidth| are used to retrieve values of target types:

> glayout :: (Layout :<: e) => e -> ((Size -> Size) -> [[(Size, Size)]])
> glayout = unlayout . inter

We can easily compose algebras together to form compositional interpretations. 
For example, we can obtain the interpretations for 'layout', 'wellSized' and 'width'
if we compose the corresponding three algebras together:

> compAlg = layoutAlg <+> wsAlg <+> widthAlg

The compositional interpretation is simply:

> evalC :: Circuit -> Compose Layout (Compose WellSized Width)
> evalC = fold compAlg

Individual interpretations can then be recovered as:

> layout :: Circuit -> ((Size -> Size) -> [[(Size, Size)]])
> layout = glayout . evalC 
>
> wellSizedC :: Circuit -> Bool
> wellSizedC = gwellSized . evalC
>
> widthC :: Circuit -> Size
> widthC = gwidth . evalC

\noindent Our approach seamlessly models the circuit layout using the 
above |layoutAlg|, with full support for compositionality and modularity.

In this section we show that our technique can be used to express multiple, 
dependent and context-sensitive interpretations in a fully modular way while
maintaining their compositionality. 
In the next section, we show how our technique is applied together with 
``\emph{Datatypes \`a la Carte}"~\cite{swierstra08} to support two-dimensional extensibility.
