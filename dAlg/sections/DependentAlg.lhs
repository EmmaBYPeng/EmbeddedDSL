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
> import MultipleAlg

%endif

Traditional approaches to preserve compositionality for dependent interpretations
also suffer from the loss of modularity. For instance, |wellSized| captures the 
property of whether a circuit is well-formed or not. It is non-compositional in the 
sense that it depends on the widths of a circuit's constituent parts. To make the 
dependent interpretation of |wellSized| compositional, Gibbons and Wu again used 
the fold-algebra with pairs~\cite{gibbons14}:

> type WellSized' = Bool 

> wswAlg :: CircuitAlg (WellSized', Width')
> wswAlg (IdentityF w)    = (True, w)
> wswAlg (FanF w)         = (True, w)
> wswAlg (AboveF x y)     = (fst x && fst y && snd x == snd y, snd x)
> wswAlg (BesideF x y)    = (fst x && fst y, snd x + snd y)
> wswAlg (StretchF ws x)  = (fst x && length ws == snd x, sum ws)

Similar to multiple interpretation with pairs, though simple, this approach is 
clumsy and not modular. On the other hand, using our technique, the algebra for
|wellSized| can be defined independently. The only restriction is that both 
|WellSized| and |Width| need to be members of the input type of |wsAlg|:

> newtype WellSized = WellSized {unwellSized :: Bool}

> wsAlg :: (WellSized :<: r, Width :<: r) => GAlg r WellSized
> wsAlg (IdentityF w)    = WellSized True
> wsAlg (FanF w)         = WellSized True
> wsAlg (AboveF x y)     = WellSized (gwellSized x && gwellSized y && gwidth x == gwidth y)
> wsAlg (BesideF x y)    = WellSized (gwellSized x && gwellSized y)
> wsAlg (StretchF xs x)  = WellSized (gwellSized x && length xs == gwidth x)

> gwellSized :: (Width :<: e, WellSized :<: e) => e -> Bool
> gwellSized = unwellSized . inter

  
\noindent Since |Width| needs to a member of the input type of |wsAlg|, we can 
now compose |wsAlg| together with |widthAlg| to support compositional interpretation
with fold:

> compAlgD = wsAlg <+> widthAlg

> evalD :: Circuit -> Compose WellSized Width
> evalD = fold compAlgD

\noindent |evalD| gives the interpretation result for both 'width' and 'wellSized', 
with the individual interpretation for 'wellSized' defined as:

> wellSized :: Circuit -> Bool
> wellSized = gwellSized . evalD 

Modular definition of algebra followed by composition using |<+>| \textemdash
modularity and compositionality are at your service!
