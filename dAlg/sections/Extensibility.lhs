%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{Extensibility in Both Dimensions}
\label{sec:extensibility}

So far we have only talked about extensibility in one dimension, namely, 
how to add new observation functions in a modular way with algebras for our DSL.
What if we want to extend our grammer by adding new constructors, which also brings
in dependencies at the same time? In this sections, we will show that our approach of
composing algebras while incorporating dependencies works well with the 
Modular Refiable Matching (MRM) approach, which allows us to add additional 
constructors modularly.

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
is no dependent on the width of its parts. However, we will keep our 
representation for dependent algebras to be consistent with the algera we will define
later for extended datatypes. 

> type GAlgB r a = CircuitFB r -> a

{\em widthAlgB} and {\em wsAlg} are also exactly the same as before:

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
{\em Stretch}. We add the datatype constructors as a functor {\em CircuitFE}: 

> data CircuitFE r = 
>     Above r r
>   | Stretch [Int] r
>   deriving Functor

Algebras correspond to this functor are similar to the ones above. The only difference
is that the interpretation for checking if a circuit is well formed depends on the 
widths of its part. Same as in section 6, we use {\em gwidth} to retrieve the width
of a circuit:

> type GAlgE r a = CircuitFE r -> a

> widthAlgE :: (Width2 :<: r) => CircuitFE r -> Width2
> widthAlgE (Above x y)    = Width2 (gwidth x)
> widthAlgE (Stretch xs x) = Width2 (sum xs)

> wsAlgE :: (Width2 :<: r, WellSized2 :<: r) => 
>           CircuitFE r -> WellSized2
> wsAlgE (Above x y)    = 
>   WellSized2 (gwellSized x && gwellSized y && gwidth x == gwidth y)
> wsAlgE (Stretch xs x) = 
>   WellSized2 (gwellSized x && length xs == gwidth x)

Unlike the |<+>| operator defined in previous sections, here we associate it with a
type class to compose algebras correponding to different functors. With this approach,
we don't have to define a different operator for algebra composition each time a 
new functor is added. Instead, all we have to do is to make a new instance of 
type class {\em Comb} and define the corresponding behavior of |<+>|.

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

> -- Sample circuit
> c1 = above (beside (fan 2) (fan 2)) 
>            (above (stretch [2, 2] (fan 2))
>                   (beside (identity 1) (beside (fan 2) (identity 1)))) 

> type Circuit2 = Fix '[CircuitFB, CircuitFE]

%endif

> compAlgB = widthAlgB <+> wsAlgB
> compAlgE = widthAlgE <+> wsAlgE

> eval :: Circuit2 -> Compose Width2 WellSized2
> eval = fold (compAlgB ::: (compAlgE ::: Void))

> width3 :: Circuit2 -> Int
> width3 = gwidth . eval 

> wellSized3 :: Circuit2 -> Bool
> wellSized3 = gwellSized . eval




