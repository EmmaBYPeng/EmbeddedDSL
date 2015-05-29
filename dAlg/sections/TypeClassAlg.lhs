%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{Other Implementations for the Circuit DSL}

Apart from using fold as F-Algebras, our technique also applies to various other 
implementations of the circuit DSL. We present one approach using type classes, 
and show how compositionality and modularity are supported in this case.

\subsection{Type Class with Proxies}
\label{sec:type-class-proxies}

%if False

> {-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators 
>  -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances 
>  -XScopedTypeVariables -XUndecidableInstances #-}

> module TypeClass where

> import FAlg hiding (Circuit, identity, fan, above, beside, stretch)
> import DependentAlg

%endif

One way to represent the circuit is to use a type class. Each interpretation 
corresponds to an instance of the type class for the type of that interpretation.
The two class type variables stand for input and output domains of an 
interpretation: 

> class Circuit inn out where
>   identity :: Proxy inn -> Int -> out
>   fan      :: Proxy inn -> Int -> out
>   above    :: inn       -> inn -> out
>   beside   :: inn       -> inn -> out
>   stretch  :: [Int]     -> inn -> out

Due to the restriction of Haskell's type classes, all class type variables must be 
reachable from the free variables of each method type. Therefore, we need the
{\em Proxy} here for {\em identity} and {\em fan} to allow the use of class type 
{\em inn}:  

> data Proxy a = Proxy

For example, the interpretation for {\em width} can be defined as:

> instance (Circuit inn Width, Width:<: inn) => Circuit inn Width where
>   identity (Proxy :: Proxy inn) w  = Width w
>   fan      (Proxy :: Proxy inn) w  = Width w
>   above x y                        = Width(gwidth x)
>   beside x y                       = Width(gwidth x + gwidth y)
>   stretch xs x                     = Width(sum xs)

Similar to using F-Algebra, dependent interpretation like |wellSized| can be defined 
as follows, with restrictions on its input type: 

> instance (Circuit inn WellSized, Width :<: inn, WellSized :<: inn) => Circuit inn WellSized where
>   identity (Proxy :: Proxy inn) w  = WellSized True
>   fan      (Proxy :: Proxy inn) w  = WellSized True
>   above x y     = WellSized (gwellSized x && gwellSized y && gwidth x == gwidth y)
>   beside x y    = WellSized (gwellSized x && gwellSized y)
>   stretch xs x  = WellSized (gwellSized x && length xs == gwidth x)

Instead of using a composition operator, we make another instance for interpretations
with composed type:

> instance (Circuit inn inn1, Circuit inn inn2) => Circuit inn (Compose inn1 inn2) where
>   identity (Proxy :: Proxy inn) w  = ((identity (Proxy :: Proxy inn) w), (identity (Proxy :: Proxy inn) w))
>   fan      (Proxy :: Proxy inn) w  = ((fan (Proxy :: Proxy inn) w), (fan (Proxy :: Proxy inn) w))
>   above x y     = ((above x y)   , (above x y))
>   beside x y    = ((beside x y)  , (beside x y))
>   stretch xs x  = ((stretch xs x), (stretch xs x))

Here we support interpretations for composed type by making the output of member 
functions a pair. The first element in the pair represents the interpretation for the
first type {\em inn1}, while the second represents the interpretation for {\em inn2}.

For example, if we want to have an interpretation for type 
{\em (Compose Width WellSized)}, we annotate each member function with type 
{\em ComposedType} to associate it with the instance of interpretation for 
composed types:

> type ComposedType = Compose Width WellSized

> gfan w         =  fan (Proxy :: Proxy ComposedType) w       :: ComposedType
> gidentity w    =  identity (Proxy :: Proxy ComposedType) w  :: ComposedType 
> gbeside x y    = (beside x y)                               :: ComposedType
> gabove x y     = (above x y)                                :: ComposedType
> gstretch xs x  = (stretch xs x)                             :: ComposedType

The circuit in Figure~\ref{fig:circuit2} can be constructed as:

> c2 = 
>   (gfan 2 `gbeside` gfan 2) `gabove`
>   gstretch [2,2] (gfan 2) `gabove`
>   (gidentity 1 `gbeside` gfan 2 `gbeside` gidentity 1)

We can project individual interpretations out using {\em gwidth} and {\em gwellSized}:

> test1 = gwidth c2
> test3 = gwellSized c2



