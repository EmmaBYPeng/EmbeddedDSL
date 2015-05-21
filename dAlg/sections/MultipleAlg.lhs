%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt


\subsection{Multiple Interpretations}
\label{sec:multiple}

%if False

> {-# OPTIONS
>  -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses
>  -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
>  -XNoMonomorphismRestriction -XDeriveFunctor -XExistentialQuantification
>  -XRankNTypes #-}

> module MultipleAlg where
> import FAlg

%endif

> compAlg = widthAlg <+> depthAlg

> eval :: Circuit -> Compose Width Depth
> eval = fold compAlg

> widthM :: Circuit -> Int
> widthM = gwidth . eval

> depthM :: Circuit -> Int
> depthM = gdepth . eval
