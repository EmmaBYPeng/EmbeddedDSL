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

Our first goal is to compose algebras modularly. It will work as the 
foundation for letting us to bring in dependent interpretions in later sections. 
By composing two algebras together, we can get a new algebra with a carrier
type containing the types of its components. 
In this section, we will use algebras for {\em width} and {\em depth} as examples 
and show how we can compose the two together.

Since a composed algebra has a composed carrier type, instead of using {\em Width} 
and {\em Depth} defined earlier to represent the semantic domain of each 
interpretation, we make use of the {\em newtype} wrapper to allow multiple 
interpretations over the same underlying type:
  
> newtype Width2 = Width2 {width :: Int}
> newtype Depth2 = Depth2 {depth :: Int}

Algebras can be defined in the same way as before:

> widthAlg2 :: CircuitAlg Width2
> widthAlg2 (IdentityF w)   = Width2 w
> widthAlg2 (FanF w)        = Width2 w
> widthAlg2 (AboveF x y)    = Width2 (width x)
> widthAlg2 (BesideF x y)   = Width2 (width x + width y)
> widthAlg2 (StretchF xs x) = Width2 (sum xs)

> depthAlg2 :: CircuitAlg Depth2
> depthAlg2 (IdentityF w)   = Depth2 0
> depthAlg2 (FanF w)        = Depth2 1
> depthAlg2 (AboveF x y)    = Depth2 (depth x + depth y)
> depthAlg2 (BesideF x y)   = Depth2 (depth x `max` depth y)
> depthAlg2 (StretchF xs x) = Depth2 (depth x)

Next we introduce the following type class to state a membership relationship
between type i and e:

> class i :<: e where
>   inter :: e -> i

Here |i :<: e| means that type i is a component of a larger collection of types 
represented by e, and gives the corresponding projection functions:

> instance i :<: i where
>   inter = id

> instance i :<: (Compose i i2) where
>   inter = fst

> instance (i :<: i2) => i :<: (Compose i1 i2) where
>   inter = inter . snd

To actually compose two algebras together, we define the operator |(<+>)|: 

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

|(<+>)| takes two algebras with carrier types |a| and |b| as inputs and gives back an 
algebra with a composed carrier type |(Compose a b)|. For {\em AboveF}, {\em BesideF}
and {\em StretchF}, their children |x| and |y| are of type |e|, where |Width2 :<: e|
and |WellSized2 :<: e|. Therefore, in the output tuple, |inter x| and |inter y| will 
have types correspond to the carrier type of a1 and a2 respectively. 

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

We can define the evaluation function of our circuit as a {\em fold}:

> eval = fold cAlg

To retrieve a target evaluation type from a composed type, we define {\em gwidth} and
{\em gdepth}: 

> gwidth :: (Width2 :<: e) => e -> Int
> gwidth = width . inter

> gdepth :: (Depth2 :<: e) => e -> Int
> gdepth = depth . inter

\noindent Now the individual interpretations can be defined as:

> width3 :: Circuit -> Int
> width3 = gwidth . eval 

> depth3 :: Circuit -> Int
> depth3 = gdepth . eval  

They can be used to evaluate the Brent-Kung parallel prefix circuit we defined in 
section 3:

> test1 = width3 c1
> test2 = depth3 c1






