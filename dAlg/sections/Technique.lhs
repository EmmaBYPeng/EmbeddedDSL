%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

%if False

> {-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators 
>             -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances 
>             -XNoMonomorphismRestriction -XDeriveFunctor 
> #-}

> module Compositionality where 

> import Introduction

%endif

\section{Compositionality with Modularity of Interpretations}
\label{sec:technique}

%if False

Another approach to represent arithmetic expressions is to used folds and 
F-Algebras~\cite{}. The shape of the expression is given by functor |ExpF| as
follows:\bruno{Maybe we should already use this in the introduction}

< data ExpF r = Lit Int | Add r r deriving Functor

|ExpF| abstracts the recursive occurrences of the datatype away, using a type 
parameter r. We can then recover the datatype using a fixpoint:

< data Exp = In (ExpF Exp)

The fold for |Exp| is defined as:

< type ExpAlg a = ExpF a -> a
<
< foldExp' :: ExpAlg a -> Exp -> a
< foldExp' alg (In x) = alg (fmap (foldExp' alg) x)

Here |GExpAlg| stands for generic algebra. It consists of two types |r| and |a|, 
and a function taking |ExpF| of r-values to an a-value. The idea is to distinguish 
between the uses of carrier types with respect to whether they are inputs (|r|) or 
outputs (|a|)~\cite{oliveira13}.
|ExpAlg| is a particular case of |GExpAlg| where the input type is the same as the 
output type.

%endif

The key idea that allows non-trivial compositional interpretations to
be defined in a modular way is an abstraction over product types,
supporting projections from a compound state space:

%format inter = "\Varid{pr}"

> class a :<: b where
>   inter :: b -> a
>
> instance a :<: a where
>   inter = id
>
> instance a :<: (a,b) where
>   inter = fst
>
> instance (c :<: b) => c :<: (a,b) where
>   inter = inter . snd

\noindent |a :<: b| means that type |a| is a component of a larger
collection of types represented by |b|. The member function |inter|
retrieves a value of type |a| from a value of the compound type |b|.
The three instances, which are defined using overlapping instances, 
define the behaviour of the projection function by searching for 
the type being projected in a larger state space that contains 
a value of that type. 

This type class was introduced by Bahr in his work on \emph{modular 
tree automata}, where he has used it to define product automata's. 
However this technique is clearly useful 

The problem of lack of modular interpretations when working with
F-algebras has been noted before. For example, in the context of
Object-Oriented Programming (OOP) the problem arises with Object
Algebras~\cite{oliveira12}: an isomorphic representation of
F-Algebras. 

In OOP languages supporting intersection types a
compositional and modular solution is possible~\cite{oliveira13}.
However, Haskell (and many other functional languages) do not support
intersection types, so that solution cannot be directly ported.
However, Haskell offers another way out using type classes. 
 
Before showing how specific algebras are defined for |Exp|, we introduce the 
following type class to state a membership relationship between type i and e
~\cite{bahr15}:



> type Compose i1 i2 = (i1, i2)

The type class gives the following projection functions:



\noindent For an algebra of type |GExpAlg r a|, its output type |a| needs to be a 
member of its intput type |r| (i.e. |a :<: r|).
For example, the algebra for evaluation can be defined as follows:

> type GExpAlg r a = ExpF r -> a
>
> evalAlg :: (Int :<: r) => GExpAlg r Int
> evalAlg (Lit x)      = x
> evalAlg (Add e1 e2)  = geval e1 + geval e2
>
> geval :: (Int :<: e) => e -> Int
> geval = inter

Here |geval| is a helper function that helps us retrieve the target value of type 
|Int| from a value of the composed type |r|.
For non-compositional interpreation like |printEval|, instead of defining |printEval|
and |eval| together as a fold-algebra using pairs, we simply specify that |Int|
(output type of |eval|) and |String| (output type of |printEval|) are both members of
the input type of the algebra for |printEval|:

> printEvalAlg :: (Int :<: r, String :<: r) => GExpAlg r String
> printEvalAlg (Lit x)      = show x
> printEvalAlg (Add e1 e2)  = 
>   "(" ++ peval e1 ++ "+" ++ peval e2 ++ ")" where
>       peval e = gprint e ++ "@" ++ show (geval e) 
>
> gprint :: (String :<: e) => e -> String
> gprint = inter

Since |Int| needs to be a member of the input type of |printEvalAlg|, when it comes 
to building compositional interpretations, we first need the following 
generic composition operator to compose algebras together. 
Given an algebra of type |GExpAlg r a| and another one of type |GExpAlg r b|, 
it gives back a composed algebra of type |GExpAlg r (Compose a b)|:

> infixr <+>
>
> (<+>) :: (a :<: r, b :<: r) => GExpAlg r a -> GExpAlg r b -> GExpAlg r (Compose a b)
> (<+>) a1 a2 fa    = (a1 fa, a2 fa)

After composing |evalAlg| and |printEvalAlg|, we can then use the composed algebra
|compAlg| to form the interpretation function |compEval| with $fold$. It is  
compositionl and provides us with results for both |eval| and |printEval|:

> compAlg = evalAlg <+> printEvalAlg
> 
> compEval :: Exp -> Compose Int String
> compEval = foldExp compAlg

%if False

> lit        = In . Lit
> add e1 e2  = In (Add e1 e2)
>
> e1 = add (add (lit 4) (lit 5)) (lit 1)

%endif

\noindent Target values are retrieved with helper functions |geval| and |gprint|: 

> eval :: Exp -> Int
> eval       = geval . compEval 
>
> printEval :: Exp -> String
> printEval  = gprint . compEval

As shown above, with our approach, to add any extra interpretation for a given 
datatype, whether it depends on other interpretations or not, all we need to do is 
to define its corresponding algebra, compose it with others using |<+>| if 
dependencies are involved, and compositional interpretations can be formed with 
$fold$. 
