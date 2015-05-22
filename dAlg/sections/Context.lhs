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
> import MultipleAlg

%endif

Connections between vertical wires of a circuit can be modeled by dividing the circuit
into different layers, with local connections only go rightwards from one layer to 
the next. Gibbons and Wu modeled such layering layout of a circuit using the 
following context-sensitive interpretation:

> type Layout' = [[(Size, Size)]]

> tlwAlg :: CircuitAlg ((Size -> Size) -> Layout', Width')
> tlwAlg (IdentityF w)    = (\f -> [], w)
> tlwAlg (FanF w)         = (\f -> [[(f 0, f i) | i <- [1..w-1]]], w)
> tlwAlg (AboveF x y)     = (\f -> fst x f ++ fst y f, snd x)
> tlwAlg (BesideF x y)    = (\f -> lzw (++) (fst x f) (fst y ((snd x +) . f)), snd x + snd y)
> tlwAlg (StretchF ws x)  = (\f -> fst x (pred . (vs!!) . f), sum ws) 
>   where vs = scanl1 (+) ws 

> lzw :: (a -> a -> a) -> [a] -> [a] -> [a]
> lzw f [] ys         = ys
> lzw f xs []         = xs
> lzw f (x:xs) (y:ys) = f x y : lzw f xs ys

|f| here is an accumulating parameter, which in this case, represents a 
transformation on wire indices.
Since the layout of a circuit depends the widths of its constituent parts, the 
interpretation for layout is dependent and needs to be paired up with the 
interpretation of width to maintain compositionality. 

\noindent Again, our approach seamlessly models the circuit layout using the 
following |layoutAlg|, with support for both compositionality and modularity:

> newtype Layout = Layout {unlayout :: (Size -> Size) -> [[(Size, Size)]]}

> layoutAlg :: (Width :<: r, Layout :<: r) => GAlg r Layout
> layoutAlg (IdentityF w)    = Layout (\f -> [])
> layoutAlg (FanF w)         = Layout (\f -> [[(f 0, f i) | i <- [1..w-1]]])
> layoutAlg (AboveF x y)     = Layout (\f -> (glayout x f ++ glayout y f))
> layoutAlg (BesideF x y)    = Layout (\f -> lzw (++) (glayout x f) (glayout y (((gwidth x)+) . f)))
> layoutAlg (StretchF xs x)  = Layout (\f -> glayout x (pred . ((scanl1 (+) xs)!!) . f))

> glayout :: (Layout :<: e) => e -> ((Size -> Size) -> [[(Size, Size)]])
> glayout = unlayout . inter

> compAlg = layoutAlg <+> widthAlg

> evalC :: Circuit -> Compose Layout Width
> evalC = fold compAlg

> layout :: Circuit -> ((Size -> Size) -> [[(Size, Size)]])
> layout = glayout . evalC 

