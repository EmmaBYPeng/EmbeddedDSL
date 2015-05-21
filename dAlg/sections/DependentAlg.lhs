%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{Dependent Algebras}
\label{sec:dependentAlg}

In the previous section we talked about how algebras can be composed together to allow
multiple interpretations. In this section, we will introduce an approach that allows 
dependent interpretations. With our approach, each property we want 
to evaluate has a corresponding algebra. There is no need to construct a pair of 
interpretations when one depends on the other. 
For example, unlike |wswAlg| in section 4.1, we have |wsAlg| that corresponds to 
{\em wellSized}, where the definition of |widthAlg| is no longer needed. 

%if False

> {-# OPTIONS
>  -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses
>  -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
>  -XNoMonomorphismRestriction -XDeriveFunctor #-}

> module DependentAlg where

> import FAlg 

%endif

For |wsAlg|, the first type |r| represents a collection of types containing
both |WellSized2| and |Width2| (specified by |(WellSized2 :<: r, Width2 :<: r)|). 
Since each child of |AboveF|, |BesideF| and |StretchF| is of type r, 
|gwidth| can be used to retrieve the width of a circuit. Therefore, |wsAlg| can be
defined as follows:

> newtype WellSized = WellSized {unwellSized :: Bool}

> wsAlg :: (WellSized :<: r, Width :<: r) => GAlg r WellSized
> wsAlg (IdentityF w)   = WellSized True
> wsAlg (FanF w)        = WellSized True
> wsAlg (AboveF x y)    = 
>   WellSized (gwellSized x && gwellSized y && 
>   gwidth x == gwidth y)
> wsAlg (BesideF x y)   =
>   WellSized (gwellSized x && gwellSized y)
> wsAlg (StretchF xs x) = 
>   WellSized (gwellSized x && length xs == gwidth x)

> gwellSized :: (Width :<: e, WellSized :<: e) => e -> Bool
> gwellSized = unwellSized . inter

Since {\em Width2} needs to be part of the carrier type of wsAlg such that we can
retreive the width of a circuit and test if it is well-formed, we need to compose 
{\em widthAlg3} and {\em wsAlg} together for evaluation. 
While the |(<+>)| operator is very similar to the one defined in the previous section,
we need to specify the relationships between types of algebras we are compsoing. 
Given an algebra from type r to type a, and another from type r to type b, 
where r contains both a and b, it gives back a new algebra from type r to type 
|(Compose a b)|.
  
Now we can define |cAlg2| that is composed of |widthAlg3| and |wsAlg|:

> cAlg2 = widthAlg <+> wsAlg

\noindent With observation functions |width2| and |wellSized2| defined as:

> width2 :: Circuit -> Int
> width2 x = gwidth (fold cAlg2 x) 

> wellSized2 :: Circuit -> Bool
> wellSized2 x = gwellSized (fold cAlg2 x) 

