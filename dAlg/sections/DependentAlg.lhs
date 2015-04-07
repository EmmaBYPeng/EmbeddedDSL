%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{Dependent Algebras}
\label{sec:dependentAlg}

In the previous section we talked about how algebras can be composed together to allow
multiple interpretations. In this section, we will introduce an approach that allows 
multiple interpretations with dependencies. With our approach, each property we want 
to evaluate has a corresponding algebra. There is no need to construct a pair of 
interpretations when one depends on the other. 
For example, unlike |wswAlg| in section 4.1, we have |wsAlg| that corresponds to 
|wellSized|, where the definition of |widthAlg| is no longer needed. 

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
> type Compose i1 i2 = (i1, i2)

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

> newtype Width2 = Width2 {width :: Int}
> newtype Depth2 = Depth2 {depth :: Int}

%endif

The first step is to change our definition of alegebra from |CircuitAlg| to |GAlg|:
> type GAlg r a = CircuitF r -> a
|GAlg| consists of two types |r| and |a|, and a function taking |CiruictF| of 
r-vlaues to an a-value, where |a :<: r|.
For |wsAlg|, the first type |r| represents a collection of types that contains 
both |WellSized2| and |Width2|. Since each child of |AboveF|, |BesideF| and |StretchF|
is of type r (specified by |(WellSized2 :<: r, Width2 :<: r)|), 
|gwidth| can be used to retrieve the width of a circuit. Therefore, |wsAlg| can be
defined as follows:

%if False

> widthAlg2 :: (Width2 :<: r) => GAlg r Width2
> widthAlg2 (IdentityF w)   = Width2 w
> widthAlg2 (FanF w)        = Width2 w
> widthAlg2 (AboveF x y)    = Width2 (gwidth x)
> widthAlg2 (BesideF x y)   = Width2 (gwidth x + gwidth y)
> widthAlg2 (StretchF xs x) = Width2 (sum xs)

%endif

> newtype WellSized2 = WellSized2 {wellSized :: Bool}

> wsAlg :: (WellSized2 :<: r, Width2 :<: r) => GAlg r WellSized2
> wsAlg (IdentityF w)   = WellSized2 True
> wsAlg (FanF w)        = WellSized2 True
> wsAlg (AboveF x y)    = 
>   WellSized2 (gwellSized x && gwellSized y && gwidth x == gwidth y)
> wsAlg (BesideF x y)   =
>   WellSized2 (gwellSized x && gwellSized y)
> wsAlg (StretchF xs x) = 
>   WellSized2 (gwellSized x && length xs == gwidth x)

Here we also need the |(<+>)| operator for composing two algebras together to allow
dependent interpretations with |fold|. 
While it is very similar to the one defined in the previous section, we need to 
specify the relationships between types of algebras we are compsoing. 
Given an algebra from type r to type a, and another from type r to type b, 
where r contains both a and b, it gives back a new algebra from type r to type 
|(Compose a b)|.
  
> (<+>) :: (a :<: r, b :<: r) => GAlg r a -> GAlg r b -> 
>                                GAlg r (Compose a b)
> (<+>) a1 a2 (IdentityF w)   = 
>   (a1 (IdentityF w), a2 (IdentityF w))
> (<+>) a1 a2 (FanF w)        = 
>   (a1 (FanF w), a2 (FanF w))
> (<+>) a1 a2 (AboveF x y)    = 
>   (a1 (AboveF (inter x) (inter y)), a2 (AboveF (inter x) (inter y)))
> (<+>) a1 a2 (BesideF x y)   = 
>   (a1 (BesideF (inter x) (inter y)), a2 (BesideF (inter x) (inter y)))
> (<+>) a1 a2 (StretchF xs x) = 
>   (a1 (StretchF xs (inter x)), a2 (StretchF xs (inter x)))

%if False

> class i :<: e where
>   inter :: e -> i

> instance i :<: i where
>   inter = id

> instance i :<: (Compose i i2) where
>   inter = fst

> instance (i :<: i2) => i :<: (Compose i1 i2) where
>   inter = inter . snd
 
> gwidth :: (Width2 :<: e) => e -> Int
> gwidth = width . inter

> gdepth :: (Depth2 :<: e) => e -> Int
> gdepth = depth . inter

> gwellSized :: (WellSized2 :<: e) => e -> Bool 
> gwellSized = wellSized . inter

%endif

Now we can define |cAlg2| that is composed of |widthAlg2| and |wsAlg|:

> cAlg2 = widthAlg2 <+> wsAlg

%if False

> -- Sample circuit
> c1 = above (beside (fan 2) (fan 2)) 
>            (above (stretch [2, 2] (fan 2))
>                   (beside (identity 1) (beside (fan 2) (identity 1)))) 

%endif

\noindent With observation functions |width2| and |wellSized2| defined as:

> width2 :: Circuit -> Int
> width2 x = gwidth (fold cAlg2 x) 

> wellSized2 :: Circuit -> Bool
> wellSized2 x = gwellSized (fold cAlg2 x) 

