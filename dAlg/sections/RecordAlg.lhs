%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\subsection{Records}
\label{sec:records}

\bruno{Maybe records are not too interesting. Type classes may be nicer to show.
Could discuss intead: 1) Datatypes a la carte + approach; 2) Simple grammar
example showing how to deal with binders.}

Alternatively, circuits can be represented using records. 

%if False

> {-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators 
>  -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances 
>  -XIncoherentInstances -XNoMonomorphismRestriction -XDeriveFunctor #-}

> module Record where

> import FAlg hiding (Circuit, identity, fan, above, beside, stretch)
> import DependentAlg

%endif

\noindent We define the following datatype with record syntax for circuit 
constructions:

> data Circuit inn out = Circuit {
>   identity  :: Int -> out,
>   fan       :: Int -> out,
>   above     :: inn -> inn -> out,
>   beside    :: inn -> inn -> out,
>   stretch   :: [Int] -> inn -> out
> }

Each interpretation corresponds to a value of the datatype. For example, for the 
interpretations of {\em width} and {\em wellSized}, we define two values {\em widthAlg} 
and {\em wsAlg}:

> widthAlg :: (Width :<: inn) => Circuit inn Width 
> widthAlg = Circuit {
>   identity  = \w    -> Width w,
>   fan       = \w    -> Width w,
>   above     = \x y  -> Width (gwidth x),
>   beside    = \x y  -> Width (gwidth x + gwidth y),
>   stretch   = \xs x -> Width (sum xs)
> }

> wsAlg :: (Width :<: inn, WellSized :<: inn) => Circuit inn WellSized
> wsAlg = Circuit {
>   identity  = \w    -> WellSized True,
>   fan       = \w    -> WellSized True,
>   above     = \x y  -> WellSized (gwellSized x && gwellSized y && gwidth x == gwidth y),
>   beside    = \x y  -> WellSized (gwellSized x && gwellSized y),
>   stretch   = \xs x -> WellSized (gwellSized x && length xs == gwidth x)
> }

Circuit composition is also defined as a value of the datatype:

> (<+>) :: (inn1 :<: inn, inn2 :<: inn) => Circuit inn inn1 -> Circuit inn inn2 -> Circuit inn (Compose inn1 inn2)
> (<+>) a1 a2 = Circuit {
>   identity  = \w    -> (identity a1 w, identity a2 w),
>   fan       = \w    -> (fan a1 w, fan a2 2),
>   above     = \x y  -> (above a1 (inter x) (inter y), above a2 (inter x) (inter y)),
>   beside    = \x y  -> (beside a1 (inter x) (inter y), beside a2 (inter x) (inter y)),
>   stretch   = \xs x -> (stretch a1 xs (inter x), stretch a2 xs (inter x))
> }


\noindent Now we can compose interpretations smoothly. For example, {\em widthAlg} and 
{\em wsAlg} can be composed together as follows:

> cAlg :: Circuit (Compose Width WellSized) (Compose Width WellSized)
> cAlg = widthAlg <+> wsAlg

Each construct is associated with the corresponding field in cAlg:

> cidentity  = identity cAlg
> cfan       = fan cAlg
> cabove     = above cAlg
> cbeside    = beside cAlg
> cstretch   = stretch cAlg

The circuit in Figure~\ref{fig:circuit2} can be constructed as follows:

> c = 
>   (cfan 2 `cbeside` cfan 2) `cabove`
>   cstretch [2,2] (cfan 2) `cabove`
>   (cidentity 1 `cbeside` cfan 2 `cbeside` cidentity 1)

%if False

> width4 :: (Width :<: e) => e -> Int
> width4 = gwidth

> wellSized4 :: (WellSized :<: e) => e -> Bool
> wellSized4 = gwellSized

%endif

\noindent |width| and |wellSized| property of c can be obtained directly using 
{\em gwidth} and {\em gwellSized}.



