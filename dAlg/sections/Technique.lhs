%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

%if False

> {-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators 
>             -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances 
>             -XIncoherentInstances -XNoMonomorphismRestriction -XDeriveFunctor 
> #-}

%endif

\section{Compositionality plus Modularity}
\label{sec:technique}

Instead of algebraic datatypes, we represent the arithmetic expressions using fold 
as F-Algebras~\cite{}. The shape of the expression is given by functor |ExpF| as
follows:

> data ExpF r = LitF Int | AddF r r deriving Functor

|ExpF| abstracts the recursive occurrences of the datatype away, using a type 
parameter r. We can then recover the datatype using a fixpoint:

> data Exp = In (ExpF Exp)

The fold for |Exp| is defined as:

> type GExpAlg r a = ExpF r -> a
> type ExpAlg a = GExpAlg a a 

> foldExp' :: ExpAlg a -> Exp -> a
> foldExp' alg (In x) = alg (fmap (foldExp' alg) x)

Here |GExpAlg| stands for generic algebra. It consists of two types |r| and |a|, 
and a function taking |ExpF| of r-values to an a-value. The idea is to distinguish 
between the uses of carrier types with respect to whether they are inputs (|r|) or 
outputs (|a|)~\cite{oliveira13}.
|ExpAlg| is a particular case of |GExpAlg| where the input type is the same as the 
output type. 
Before showing how specific algebras are defined for |Exp|, we introduce the 
following type class to state a membership relationship between type i and e
~\cite{bahr15}:

> class i :<: e where
>   inter :: e -> i

|i :<: e| means that type i is a component of a larger collection of types 
represented by e, while the member function |inter| retrieves a value of type i from
the collection of type e. It gives the corresponding projection functions:


> type Compose i1 i2 = (i1, i2)

> instance i :<: i where
>   inter = id

> instance i :<: (Compose i i2) where
>   inter = fst

> instance (i :<: i2) => i :<: (Compose i1 i2) where
>   inter = inter . snd

\noindent For an algebra of type |GExpAlg r a|, its output type |a| needs to be a 
member of its intput type |r| (i.e. |a :<: r|).
For example, the algebra for evaluation can be defined as follows:

> evalAlg :: (Int :<: r) => GExpAlg r Int
> evalAlg (LitF x)   = x
> evalAlg (AddF e1 e2) = geval e1 + geval e2

For non-compositional interpreation like |printEval|, instead of defining |printEval|
and |eval| together as a fold-algebra using pairs, we simply specify that |Int|
(output type of |eval|) and |String| (output type of |printEval|) are both members of
the input type of the algebra for |printEval|:

> printEvalAlg :: (Int :<: r, String :<: r) => GExpAlg r String
> printEvalAlg (LitF x) = show x
> printEvalAlg (AddF e1 e2) = 
>   "(" ++ peval e1 ++ "+" ++ peval e2 ++ ")" where
>       peval e = gprint e ++ "@" ++ show (geval e) 

|geval| and |gprint| are helper functions defined for retrieving a target type from 
a composed type |e|:

> geval :: (Int :<: e) => e -> Int
> geval = inter

> gprint :: (String :<: e) => e -> String
> gprint = inter

Since |Int| needs to be a member of the input type of |printEvalAlg|, we define the
following composition operator to compose two algebras together. Given an algebra of
type |GExpAlg r a| and another one of type |GExpAlg r b|, it gives back a composed
algebra of type |GExpAlg r (Compose a b)|

> (<+>) :: (a :<: r, b :<: r) => GExpAlg r a -> GExpAlg r b -> GExpAlg r (Compose a b)
> (<+>) a1 a2 (LitF x)    = (a1 (LitF x), a2 (LitF x))
> (<+>) a1 a2 (AddF e1 e2) = (a1 (AddF e1 e2), a2 (AddF e1 e2))

An algebra composed of |evalAlg| and |printEvalAlg| can be defined as:

> compAlg = evalAlg <+> printEvalAlg

%if False

> lit = In . LitF
> add e1 e2 = In (AddF e1 e2)

> e1 = add (add (lit 4) (lit 5)) (lit 1)

%endif

\noindent We can then define the two interpretations |eval| and |printEval| as: 

> eval      = geval . (foldExp' compAlg)
> printEval = gprint . (foldExp' compAlg)

As shown above, using our technique, algebras corresponding to different 
interpretations are defined separately. They are then composed together using the
generic composition operator |<+>| to form compositional interpretations with fold.

