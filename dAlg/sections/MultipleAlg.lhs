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

> type Width' = Int
> type Depth' = Int

> wdAlg :: CircuitAlg (Width', Depth')
> wdAlg (IdentityF w)    = (w, 0)
> wdAlg (FanF w)         = (w, 1)
> wdAlg (AboveF x y)     = (fst x, snd x + snd y)
> wdAlg (BesideF x y)    = (fst x + fst y, snd x `max` snd y)
> wdAlg (StretchF ws x)  = (sum ws, snd x)  

However, as we mention in section~\ref{sec:introduction}, this approach trades
modularity for compositionality. On the contrary, multiple interpretations can be
easily achieved using our technique, with support for both modularity and 
compositionality:

> compAlgM = widthAlg <+> depthAlg

> evalM :: Circuit -> Compose Width Depth
> evalM = fold compAlgM

\bruno{Text about these  2 steps here.}

> widthM :: Circuit -> Size
> widthM = gwidth . evalM

> depthM :: Circuit -> Size
> depthM = gdepth . evalM

|compAlg| is composed of |widthAlg| and |depthAlg|, using the composition operator 
|<+>| defined in section~\ref{sec:technique}. 
From the compositional interpretation |evalM|, it is straightforward to recover 
individual interpretations to obtain the width and depth of a circuit.

\bruno{Again too succint. Show how to use it on concrete examples? Reiterate
(some of) the benefits. Finish the section with a punchline.}
