%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

%format :- = "\mathbin{\thinspace''" : "}"
%format PATTERNS = Patterns "\mathbin{\thinspace''" [] "}"
%format Val = "{\sf Val}" 

\section{Composable Algebras}
\label{sec:composable}

%format In_f
%format extract_f
%format fmap_f

%if False

> {-# OPTIONS
>  -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses
>  -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
>  -XNoMonomorphismRestriction -XDeriveFunctor #-}

> data CircuitF r = 
>    IdentityF Int
>  | FanF Int
>  | AboveF r r 
>  | BesideF r r
>  | StretchF [Int] r
>  deriving Functor

> -- Fold and smart constructors
> type CircuitAlg a = CircuitF a -> a

> data Circuit = In (CircuitF Circuit)

> fold :: CircuitAlg a -> Circuit -> a
> fold alg (In x) = alg (fmap (fold alg) x)

> identity :: Int -> Circuit
> identity = In . IdentityF

> fan :: Int -> Circuit
> fan = In . FanF

> above :: Circuit -> Circuit -> Circuit
> above x y = In (AboveF x y)

> beside :: Circuit -> Circuit -> Circuit
> beside x y = In (BesideF x y)

> stretch :: [Int] -> Circuit -> Circuit
> stretch xs x = In (StretchF xs x)

%endif

To allow composing algebras modularly, we first use the following type class to state
that a semantic domain of type i is part of a larger collection of types:

> class i :<: e where
>   inter :: e -> i

Here |i :<: e| means that i is a component of e, and gives the corresponding 
projection functions as follows:

> instance i :<: i where
>   inter = id

> instance i :<: (Compose i i2) where
>   inter = fst

> instance (i :<: i2) => i :<: (Compose i1 i2) where
>   inter = inter . snd

Then we introduce the operator |(<+>)| that takes two algebras as inputs and gives 
back an algebra with a composed carrier type.

> type Compose i1 i2 = (i1, i2)

> (<+>) :: CircuitAlg a -> CircuitAlg b -> CircuitAlg (Compose a b)
> (<+>) a1 a2 (IdentityF w)   = (a1 (IdentityF w), a2 (IdentityF w))
> (<+>) a1 a2 (FanF w)        = (a1 (FanF w), a2 (FanF w))
> (<+>) a1 a2 (AboveF x y)    = 
>   (a1 (AboveF (inter x) (inter y)), a2 (AboveF (inter x) (inter y)))
> (<+>) a1 a2 (BesideF x y)   = 
>   (a1 (BesideF (inter x) (inter y)), a2 (BesideF (inter x) (inter y)))
> (<+>) a1 a2 (StretchF xs x) = 
>   (a1 (StretchF xs (inter x)), a2 (StretchF xs (inter x)))

Since now a circuit can be made up of subcircuits with composed semantic domain, 
we need to slightly modify our constructs of algebras. 
With the help of the {\em newtype} wrapper which is needed to allow multiple 
interpretations over the same underlying type, we define {\em gwidth} and {\em gdepth}
to help us retrieve the target evaluation type from a composed type: 

> newtype Width2 = Width2 {width :: Int}
> newtype Depth2 = Depth2 {depth :: Int}

> gwidth :: (Width2 :<: e) => e -> Int
> gwidth = width . inter

> gdepth :: (Depth2 :<: e) => e -> Int
> gdepth = depth . inter

Then we can define {\em widAlg2} and {\em depthAlg2} as:

> widthAlg2 :: CircuitAlg Width2
> widthAlg2 (IdentityF w)   = Width2 w
> widthAlg2 (FanF w)        = Width2 w
> widthAlg2 (AboveF x y)    = Width2 (gwidth x)
> widthAlg2 (BesideF x y)   = Width2 (gwidth x + gwidth y)
> widthAlg2 (StretchF xs x) = Width2 (sum xs)

> depthAlg2 :: CircuitAlg Depth2
> depthAlg2 (IdentityF w)   = Depth2 0
> depthAlg2 (FanF w)        = Depth2 1
> depthAlg2 (AboveF x y)    = Depth2 (gdepth x + gdepth y)
> depthAlg2 (BesideF x y)   = Depth2 (gdepth x `max` gdepth y)
> depthAlg2 (StretchF xs x) = Depth2 (gdepth x)
 
Now it is straightforward to compose algebras together: 
> cAlg = widthAlg2 <+> depthAlg2
|cAlg| is composed of |widthAlg2| and |depthAlg2|, with a carrier type of 
|(Compose Width2 Depth2)|.

%if False

> -- Sample circuit
> c1 = above (beside (fan 2) (fan 2)) 
>            (above (stretch [2, 2] (fan 2))
>                   (beside (identity 1) (beside (fan 2) (identity 1)))) 

%endif

\noindent The observation functions for our circuit can be defined as:

> width3 :: Circuit -> Int
> width3 x = gwidth (fold cAlg x) 

> depth3 :: Circuit -> Int
> depth3 x = gdepth (fold cAlg x) 






