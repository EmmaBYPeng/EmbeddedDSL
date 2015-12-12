%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{Extensibility in Both Dimensions}
\label{sec:extensibility}

So far we have only talked about extensibility in one dimension, namely, to add 
compositional interpretations in a modular way. 
What if we want to have extensibility in a second dimension, which is to extend our 
grammer by adding new data constructors modularly? To make the problem more 
interesting, these additional constructors bring dependent interpretations as well. 
In this section, we will show that our technique works well with the 
Modular Refiable Matching (MRM) approach\cite{oliveira15}, which allows us to add 
additional constructors modularly. 
We will present a two-level composition of algebras: for each modular component, 
we compose its algebras together if an interpretation is dependent; for different 
components, we combine their corresponding algebras together to allow evaluation of 
a composed data structure. 

%if False

> {-# OPTIONS
>  -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators 
>  -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances 
>  -XIncoherentInstances -XKindSignatures -XNoMonomorphismRestriction 
>  -XDeriveFunctor -XDataKinds -XGADTs #-}

> module Extensibility where

> import FAlg hiding (Circuit, In, (<+>), fold)
> import DependentAlg

> data Fix (fs :: [* -> *]) where
>   In :: Functor f => Elem f fs -> f (Fix fs) -> Fix fs

> data Elem (f :: * -> *) (fs :: [* -> *]) where
>   Here  :: Elem f (f ': fs)
>   There :: Elem f fs -> Elem f (g ': fs)

> class f :< fs where
>   witness :: Elem f fs
> instance f :< (f ': fs) where
>   witness = Here
> instance (f :< fs) => f :< (g ': fs) where
>   witness = There witness

> -- Smart fixpoint constructor
> inn :: (f :< fs, Functor f) => f (Fix fs) -> Fix fs
> inn = In witness

> -- The Matches datatype
> data Matches (fs :: [* -> *]) (a :: *) (b :: *) where
>   Void  :: Matches '[] a b
>   (:::) :: Functor f => (f a -> b) -> Matches fs a b -> 
>                         Matches (f ': fs) a b

> extractAt :: Elem f fs -> Matches fs a b -> (f a -> b)
> extractAt Here        (f ::: _) = f
> extractAt (There pos) (_ ::: fs) = extractAt pos fs

> match :: Matches fs (Fix fs) b -> Fix fs -> b
> match fs (In pos xs) = extractAt pos fs xs

> -- Fold for List-of-Functors Datatypes
> type Algebras fs a = Matches fs a a

> fold :: Algebras fs a -> Fix fs -> a
> fold ks (In pos xs) = extractAt pos ks (fmap (fold ks) xs)

%endif

For example, say at first we only have three constructs in our DSL of circuits: 
{\em IdentityFB}, {\em FanFB}, and {\em BesideFB}. 
We can define a functor {\em CircuitFB} to represent this datatype, where B stands 
for {\em Base}: 

> data CircuitFB r = 
>     IdentityFB Int
>   | FanFB Int
>   | BesideFB r r
>   deriving Functor

< data CircuitB = In (CircuitFB CircuitB)

For $CircuitB$, there is no dependencies involved in the interpretation for 
'wellSized' of this circuit, since with only {\em IdentityFB}, {\em FanFB} and 
{\em BesideFB}, whether a circuit is well formed or not is not dependent on the 
width of its parts. 

The generic algebra type for $CircuitB$ is:

> type GAlgB r a = CircuitFB r -> a

Algebras corresponding to the interpretations for 'width' and 'wellSized' are 
exactly the same as before:

> widthAlgB :: (Width :<: r) => CircuitFB r -> Width
> widthAlgB (IdentityFB w)   = Width w
> widthAlgB (FanFB w)        = Width w
> widthAlgB (BesideFB x y)   = Width (gwidth x + gwidth y)

> wsAlgB :: (Width :<: r, WellSized :<: r) => CircuitFB r -> WellSized
> wsAlgB (IdentityFB w)   = WellSized True
> wsAlgB (FanFB w)        = WellSized True
> wsAlgB (BesideFB x y)   = WellSized (gwellSized x && gwellSized y)

Now, suppose we want to extend our circuits by adding new constructs |AboveFB| and
|StretchFB|. We add the datatype constructors as a functor $CircuitFE$, where
E stands for $Extended$: 

> data CircuitFE r = 
>     AboveFB r r
>   | StretchFB [Int] r
>   deriving Functor

< data CircuitE = In (CircuitFE CircuitE)

For $above$ and $stretch$, the interpretation for 'wellSized' depends on the widths 
of a circuit's constituent parts. 
Same as in section~\ref{sec:f-algebra}, we use |gwidth| to retrieve the width of a 
circuit:

> type GAlgE r a = CircuitFE r -> a

> widthAlgE :: (Width :<: r) => CircuitFE r -> Width
> widthAlgE (AboveFB x y)    = Width (gwidth x)
> widthAlgE (StretchFB xs x) = Width (sum xs)

> wsAlgE :: (Width :<: r, WellSized :<: r) => 
>   CircuitFE r -> WellSized
> wsAlgE (AboveFB x y)    = 
>   WellSized (gwellSized x && gwellSized y && gwidth x == gwidth y)
> wsAlgE (StretchFB xs x) = 
>   WellSized (gwellSized x && length xs == gwidth x)

Unlike the |<+>| operator in previous sections, here we associate it with a
type class to compose algebras correponding to different functors. With this approach,
we don't have to define a different operator for algebra composition each time a 
new functor is added. Instead, all we have to do is to make a new instance of the
type class $Comb$. Since there are two functors $CircuitFB$ and $CircuitFE$, 
we create two instances of $Comb$ and define |<+>| for each of them:

> class Comb f where
>   (<+>) :: (a :<: r, b :<: r) => (f r -> a) -> (f r -> b) -> (f r -> (Compose a b))

> instance Comb CircuitFB where
>   (<+>) a1 a2 f = (a1 f, a2 f)

> instance Comb CircuitFE where
>   (<+>) a1 a2 f = (a1 f, a2 f) 

%if False

> type Circuit = Fix '[CircuitFB, CircuitFE]

%endif

A circuit with all five constructs can be built from the modular components. First
we recover the extended circuit datatype:

< type Circuit = Fix `[CircuitFB, CircuitFE]

$Circuit$ here denotes circuits that have $IdentityFB$, $FanFB$, 
$BesideFB$, $AboveFB$ and $StretchFB$ as their components. 

> compAlgE = widthAlgE <+> wsAlgE

We then use |(:::)| to combine algebras correspond to different functors together
\cite{oliveira15}. Since algebras in the list constructed by |(:::)|
need to have the same input and output type, we compose |widthAlgB| and 
|wsAlgB| for |CircuitFB| and get |compAlgB|:

> compAlgB = widthAlgB <+> wsAlgB

The fold operator defined in MRM library~\cite{oliveira15} takes an 
|fs|-algebra and |Fix fs| arguments. We define the evaluation function for our 
circuit as a fold using the combined algebras:

> evalE :: Circuit -> Compose Width WellSized
> evalE = fold (compAlgB ::: (compAlgE ::: Void))

Invidual interpretations can then be retrieved as follows:

> widthE :: Circuit -> Int
> widthE = gwidth . evalE 

> wellSizedE :: Circuit -> Bool
> wellSizedE = gwellSized . evalE

They can be used with smart constructors to evaluate a concrete circuit:

> c3 = 
>   (fan 2 `beside` fan 2) `above`
>   stretch [2, 2] (fan 2) `above`
>   (identity 1 `beside` fan 2 `beside` identity 1)

