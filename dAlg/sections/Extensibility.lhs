%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{Extensibility in Both Dimensions}
\label{sec:extensibility}

So far we have only talked about extensibility in one dimension, namely, 
how to add new observation functions in a modular way with algebras for our DSL.
What if we want to have extensibility in a second dimension, which is to extend our 
grammer by adding new data constructors modularly? To make the problem more 
interesting, these additional constructors may also bring dependencies in their 
corresponding observation functions at the same time. 
In this section, we will show that our approach of composing algebras while 
incorporating dependencies works well with the Modular Refiable Matching (MRM) 
approach, which allows us to add additional constructors modularly. We will present
a two-level composition of algebras: for each modular component, we compose its
algebras together if an interpretation is dependent; for different components, we 
combine their corresponding algebras together to allow evaluation of a composed 
data structure. 

%if False

> {-# OPTIONS
>  -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators 
>  -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances 
>  -XIncoherentInstances -XKindSignatures -XNoMonomorphismRestriction 
>  -XDeriveFunctor -XDataKinds -XGADTs #-}

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

> newtype Width2     = Width2     {width :: Int}
> newtype WellSized2 = WellSized2 {wellSized :: Bool}

%endif

For example, say at first we only have three constructs in our DSL of circuits: 
{\em Identity}, {\em Fan}, and {\em Beside}. We can define a functor {\em CircuitFB}
to represent this datatype, where B stands for {\em Base}: 

> data CircuitFB r = 
>     Identity Int
>   | Fan Int
>   | Beside r r
>   deriving Functor

There is no dependencies involved for the algebras of this ciruict, since with only
{\em Identity}, {\em Fan} and {\em Beside}, whether a circuit is well formed or not
is not dependent on the width of its parts. However, we will keep our 
representation for dependent algebras to be consistent with algeras we will later
define for extended datatypes: 

> type GAlgB r a = CircuitFB r -> a

Algebras for {\em width} and {\em wellSized} are exactly the same as before:

> widthAlgB :: (Width2 :<: r) => CircuitFB r -> Width2
> widthAlgB (Identity w)   = Width2 w
> widthAlgB (Fan w)        = Width2 w
> widthAlgB (Beside x y)   = Width2 (gwidth x + gwidth y)

> wsAlgB :: (Width2 :<: r, WellSized2 :<: r) => 
>   CircuitFB r -> WellSized2
> wsAlgB (Identity w)   = WellSized2 True
> wsAlgB (Fan w)        = WellSized2 True
> wsAlgB (Beside x y)   = WellSized2 (gwellSized x && gwellSized y)

Now suppose we want to extend our circuits by adding new constructs {\em Above} and
{\em Stretch}. We add the datatype constructors as a functor {\em CircuitFE}, where
E stands for {\em Extended}: 

> data CircuitFE r = 
>     Above r r
>   | Stretch [Int] r
>   deriving Functor

Algebras correspond to this functor are similar to the ones above. The only difference
is that the interpretation for checking if a circuit is well formed now depends 
on the widths of its part. Same as in section 6, we use {\em gwidth} to retrieve the
width of a circuit:

> type GAlgE r a = CircuitFE r -> a

> widthAlgE :: (Width2 :<: r) => CircuitFE r -> Width2
> widthAlgE (Above x y)    = Width2 (gwidth x)
> widthAlgE (Stretch xs x) = Width2 (sum xs)

> wsAlgE :: (Width2 :<: r, WellSized2 :<: r) => 
>   CircuitFE r -> WellSized2
> wsAlgE (Above x y)    = 
>   WellSized2 (gwellSized x && gwellSized y && gwidth x == gwidth y)
> wsAlgE (Stretch xs x) = 
>   WellSized2 (gwellSized x && length xs == gwidth x)

Unlike the |<+>| operator defined in previous sections, here we associate it with a
type class to compose algebras correponding to different functors. With this approach,
we don't have to define a different operator for algebra composition each time a 
new functor is added. Instead, all we have to do is to make a new instance of 
type class {\em Comb} and define the corresponding behavior of |<+>|. Since we have
two functors {\em CircuitFB} and {\em CircuitFE}, we create two instances of 
{\em Comb} and define |<+>| for each of them:

> class Comb f r a b where
>   (<+>) :: (f r -> a) -> (f r -> b) -> (f r -> (Compose a b))

> instance (a :<: r, b :<: r) =>  Comb CircuitFB r a b where
>   (<+>) a1 a2 (Identity w)   = (a1 (Identity w), a2 (Identity w))
>   (<+>) a1 a2 (Fan w)        = (a1 (Fan w), a2 (Fan w))
>   (<+>) a1 a2 (Beside x y)   = 
>     (a1 (Beside (inter x) (inter y)), a2 (Beside (inter x) (inter y)))

> instance (a :<: r, b :<: r) => Comb CircuitFE r a b where
>   (<+>) a1 a2 (Above x y)    = 
>     (a1 (Above (inter x) (inter y)), a2 (Above (inter x) (inter y)))
>   (<+>) a1 a2 (Stretch xs x) = 
>     (a1 (Stretch xs (inter x)), a2 (Stretch xs (inter x)))

%if False

> type Compose x y = (x, y)

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

> gwellSized :: (WellSized2 :<: e) => e -> Bool
> gwellSized = wellSized . inter

> identity :: (CircuitFB :< fs) => Int -> Fix fs
> identity = inn . Identity

> fan :: (CircuitFB :< fs) => Int -> Fix fs
> fan = inn . Fan

> beside :: (CircuitFB :< fs) => Fix fs -> Fix fs -> Fix fs
> beside x y = inn (Beside x y)

> above :: (CircuitFE :< fs) => Fix fs -> Fix fs -> Fix fs
> above x y = inn (Above x y)

> stretch :: (CircuitFE :< fs) => [Int] -> Fix fs -> Fix fs
> stretch xs x = inn (Stretch xs x)

> type Circuit2 = Fix '[CircuitFB, CircuitFE]

%endif

A circuit with all five constructs can be built from the modular components. First
we define the type of the circuit:

< type Circuit2 = Fix `[CircuitFB, CircuitFE]

The type {\em Circuit2} denotes circuits that have {\em Identity}, {\em Fan}, 
{\em Beside}, {\em Above} and {\em Stretch} as their components. 

Since {\em Width2} needs to be part of the carrier type of wsAlgE such that we can
retreive the width of a circuit and test if it is well-formed, for {\em CircuitFE},
we need to compose {\em widthAlgE} and {\em wsAlgE} together and use {\em compAlgE} 
for evaluation.

> compAlgE = widthAlgE <+> wsAlgE

Then we use |(:::)| to combine algebras correspond to different functors together
~\cite{Gibbons:14:Folding}. Since the algebras in the list constructed by |(:::)|
need to have the same carrier and return type, we compose {\em widthAlgB} and 
{\em wsAlgB} for {\em CircuitFB} and get {\em compAlgB}:

> compAlgB = widthAlgB <+> wsAlgB

The {\em fold} operator defined in MRM library~\cite{Gibbons:14:Folding} takes an 
|fs|-algebra and |Fix fs| arguments. We define the evaluation function for our 
circuit as a fold using the combined algebras:

> eval :: Circuit2 -> Compose Width2 WellSized2
> eval = fold (compAlgB ::: (compAlgE ::: Void))

Invidual interpretations can then be retrieved by {\em gwidth} and {\em gwellSized}:

> width3 :: Circuit2 -> Int
> width3 = gwidth . eval 

> wellSized3 :: Circuit2 -> Bool
> wellSized3 = gwellSized . eval

They can be used with smart constructors to evaluate a concrete circuit:

> circuit2 = 
>   (fan 2 `beside` fan 2) `above`
>   stretch [2, 2] (fan 2) `above`
>   (identity 1 `beside` fan 2 `beside` identity 1)

> test1 = width3 circuit2
> test2 = wellSized3 circuit2

