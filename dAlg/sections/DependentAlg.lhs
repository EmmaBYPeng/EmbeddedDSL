%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\subsection{Dependent Interpretations}
\label{sec:dependentAlg}

%if False

> {-# OPTIONS
>  -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses
>  -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
>  -XNoMonomorphismRestriction -XDeriveFunctor #-}

> module DependentAlg where

> import FAlg 

%endif

Traditional approaches to preserve compositionality for dependent interpretations
also suffer from the loss of modularity. For instance, |wellSized| captures the 
property of whether a circuit is well-formed or not. It is non-compositional in that
it depends on the widths of a circuit's constituent parts. To make the 
dependent interpretation of |wellSized| compositional, Gibbons and Wu again used 
the fold-algebra with pairs~\cite{gibbons14}:

> newtype WellSized = WellSized {unwellSized :: Bool}

> wd :: (Width, WellSized) -> Int
> wd = unwidth . fst

> ws :: (Width, WellSized) -> Bool
> ws = unwellSized . snd

> wswAlg :: CircuitAlg (Width, WellSized)
> wswAlg (IdentityF w)   = (Width w, WellSized True)
> wswAlg (FanF w)        = (Width w, WellSized True)
> wswAlg (AboveF x y)    = (Width (wd x), WellSized (ws x && ws y && wd x == wd y))
> wswAlg (BesideF x y)   = (Width (wd x + wd y), WellSized (ws x && ws y))
> wswAlg (StretchF xs x) = (Width (sum xs), WellSized (ws x && length xs == wd x))

Similar to multiple interpretation with pairs, though simple, this approach is 
clumsy and not modular. On the other hand, using our technique, the algebra for
|wellSized| can be defined independently. The only restriction is that both 
|WellSized| and |Width| need to be members of the input type of |wsAlg|:

> wsAlg :: (WellSized :<: r, Width :<: r) => GAlg r WellSized
> wsAlg (IdentityF w)   = WellSized True
> wsAlg (FanF w)        = WellSized True
> wsAlg (AboveF x y)    = WellSized (gwellSized x && gwellSized y && gwidth x == gwidth y)
> wsAlg (BesideF x y)   = WellSized (gwellSized x && gwellSized y)
> wsAlg (StretchF xs x) = WellSized (gwellSized x && length xs == gwidth x)

> gwellSized :: (Width :<: e, WellSized :<: e) => e -> Bool
> gwellSized = unwellSized . inter

  
\noindent Now we can compose |wsAlg| together with |widthAlg| to support 
compositional interpretation with fold:

> compAlgD = wsAlg <+> widthAlg

> evalD :: Circuit -> Compose Width WellSized
> evalD = fold compAlgD

\noindent Individual interpretations for |width| and |wellSized| are defined as:

> widthD :: Circuit -> Int
> widthD = gwidth . evalD 

> wellSized :: Circuit -> Bool
> wellSized = gwellSized . evalD 

