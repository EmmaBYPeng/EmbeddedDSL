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

|compAlg| is an algebra composed of |widthAlg| and |depthAlg| (defined in 
section~\ref{sec:f-algebra}), using the composition operator |<+>| defined in 
section~\ref{sec:technique}. It has a composed type of |Width| and |Depth|. 

\noindent The following |evalM| function is compositional, and will give the 
interpretation result containing both the width and depth of a circuit: 

> evalM :: Circuit -> Compose Width Depth
> evalM = fold compAlgM

From |evalM|, it is straightforward to recover the individual 'width' and 'depth'
interpretations:

> widthM :: Circuit -> Size
> widthM = gwidth . evalM

> depthM :: Circuit -> Size
> depthM = gdepth . evalM

For example, for the circuit $c_1$ defined in section~\ref{sec:f-algebra}, 
$widthM$ $c_1$ gives us its width and $depthM$ $c_1$ gives its depth. Our technique
saves us from the tedious work of defining two interpretations as one fold-algebra
using pairs, and is much more light-weight especially when we want to have more than 
two interpretations at one time. 

