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

Suppose we want to have an algebra that can give us the width and depth of a circuit 
simutaneously. Gibbons and Wu showed how such multiple interpretations could be 
acheived with the following algebra~\cite{gibbons14}, by pairing semantics up and 
projecting desired interpretations from a tuple:

> wd :: (Width, Depth) -> Int
> wd = unwidth . fst

> dp :: (Width, Depth) -> Int
> dp = undepth . snd

> wdAlg :: CircuitAlg (Width, Depth)
> wdAlg (IdentityF w)   = (Width w, Depth 0)
> wdAlg (FanF w)        = (Width w, Depth 1)
> wdAlg (AboveF x y)    = (Width (wd x),        Depth (dp x + dp y))
> wdAlg (BesideF x y)   = (Width (wd x + wd y), Depth (dp x `max` dp y))
> wdAlg (StretchF ws x) = (Width (sum ws),      Depth (dp x))  

However, as we mention in section~\ref{sec:introduction}, this approach trades
modularity for compositionality. On the contrary, multiple interpretations can be
easily achieved using our technique, with support for both modularity and 
compositionality:

> compAlgM = widthAlg <+> depthAlg

> evalM :: Circuit -> Compose Width Depth
> evalM = fold compAlgM

> widthM :: Circuit -> Int
> widthM = gwidth . evalM

> depthM :: Circuit -> Int
> depthM = gdepth . evalM

|compAlg| is composed of |widthAlg| and |depthAlg|, using the composition operator 
|<+>| defined in section~\ref{sec:technique}. 
From the compositional interpretation |evalM|, it is straightforward to recover 
individual interpretations to obtain the width and depth of a circuit.
