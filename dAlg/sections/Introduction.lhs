%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%%include Paper.fmt

%if False

> {-# OPTIONS -XDeriveFunctor #-}

> module Introduction where

%endif

\section{Introduction}
\label{sec:introduction}

%format eval1
%format eval2
%format printEval2

Functional programming languages are great for implementing DSLs. Features
such as algebraic datatypes, pattern matching and/or higher-order functions 
can be used to implement languages in a variety of ways. For example, 
one way to implement a simple language of arithmetic expressions is to 
use an algebraic datatype to capture the abstract syntax of a language:

%format AExp = "\Varid{Exp_1}"
%format LitA = "\Varid{Lit_1}"
%format AddA = "\Varid{Add_1}"

> data AExp = LitA Int | AddA AExp AExp

\noindent Using pattern matching, evaluation is then defined as follows:

> eval1 :: AExp -> Int
> eval1 (LitA x)      = x
> eval1 (AddA e1 e2)  = eval1 e1 + eval1 e2

When expressing the semantics of a languages, a desirable property is
\emph{compositionality}. Informally, compositionality means that the
semantics of a language is determined solely from the interpretations
of its parts. The definition of |eval| is compositional, since
evaluation of an expression depends only on evaluation of the
subexpressions.

As nicely illustrated by Gibbons and Wu~\cite{gibbons14}, in functional
programming \emph{folds} capture compositionality precisely.
One way to define arithmetic expressions using a fold is using F-Algebras.

> data ExpF a  = Lit Int | Add a a deriving Functor
>
> newtype Exp  = In {out :: ExpF Exp}

The first step is to define the functor for arithmetic expressions
|ExpF|. The second step is to define the recursive type |Exp2| using
the functor. Finally the fold can be defined as follows:

> type ExpAlg a = ExpF a -> a
>
> foldExp :: ExpAlg a -> Exp -> a
> foldExp alg = alg . fmap (foldExp alg) . out

%if False

For example, the fold for |Exp| is:

> {-
> type ExpAlg a = (Int -> a, a -> a -> a)
>
> foldExp :: ExpAlg a -> Exp -> a 
> foldExp (l,a) (Lit x)      = l x
> foldExp (l,a) (Add e1 e2)  = 
>    a (foldExp (l,a) e1) (foldExp (l,a) e2)  
> -}

%endif

\noindent The definition of |foldExp| captures a recursion pattern
where the result of a traversal can only depend on the recursive calls
of the subexpressions. The type |ExpAlg a| captures the fold-algebra of
the datatype.
With |foldExp| another way to define |eval| is:

> eval2 :: ExpAlg Int
> eval2 (Lit x)      = x
> eval2 (Add e1 e2)  = e1 + e2

\noindent The use of |foldExp| instead of directly using pattern
matching and general recursion, makes it obvious that the definition
is compositional.

\section{Compositionality without Modularity of Non-Trivial Interpretations}
\label{sec:nonmodular}

Certain interpretations are not trivially compositional.
While it is still possible to express those definitions with folds using 
well-known techniques, a certain degree of modularity is lost. 
For example, consider the following interpretation of expressions:

%%format printEval = "\Varid{printEval_1}"

> printEval :: AExp -> String
> printEval (LitA x)      = show x
> printEval (AddA e1 e2)  = "(" ++ peval e1 ++ " + " ++ peval e2 ++ ")" 
>    where peval e = printEval e ++ "@" ++ show (eval1 e)

\noindent The intention is to print a textual representation of the 
arithmetic expression. However there is a little twist: the values of the 
subexpressions are printed along with the textual representation.
For example, given the expression:

> e1 = Add (Add (Lit 4) (Lit 5)) (Lit 1)

\noindent the result of |printEval e1| is:

< "((4@4 + 5@5)@9 + 1@1)"

The result of |printEval| does not depend only on the recursive calls
of to the subexpressions: it also depends on |eval1|.  Thus, at first, it seems
that |printEval| is non-compositional. However, when viewed through
the right lenses, |printEval| can be considered compositional and it
is implementable as a fold. The basic idea, which is well-known and has been 
widely used in the past, is to
define the two interpretations (|printEval| and |eval1|)
simultaneously as a fold-algebra using pairs:

%format pevalAlg = "\Varid{peAlg}"

> pevalAlg :: ExpAlg (String,Int)
> pevalAlg (Lit x)      = (show x, id x)
> pevalAlg (Add e1 e2)  = (  "(" ++ peval e1 ++ " + " ++ peval e2 ++ ")", snd e1 + snd e2) 
>   where peval e    = fst e ++ "@" ++ show (snd e)

\noindent Then it is easy to obtain a version of |printEval| by simply 
applying |foldExp| to the algebra and retrieving the component of the pair 
that defines |printEval|.

> printEval2 = fst . foldExp pevalAlg

Using this simple technique Gibbons and
Wu~\cite{} have shown that various types of non-trivial interpretations 
of DSLs can be defined compositionaly. In particular they illustrate
how to model \emph{multiple}, \emph{dependent} and
\emph{context-sensitive} interpretations.
The function |printEval| is an example of a dependent interpretation:
the interpretation of subexpressions depends on another interpretation (|eval1|).


Unfortunatelly there are some problems with using pairs to combine
together multiple interpretations in an algebra. As Gibbons and Wu
point out:

\begin{quote}
But this is still a bit clumsy: it entails revising existing code
each time a new interpretation is added, and wide tuples generally
lack good language support.
\end{quote}
\vspace{5pt}

\noindent In other words the technique is \emph{non-modular}: we cannot
simply reuse |eval1| or |eval2| in the definition of
|pevalAlg|. Instead evaluation must be redefined together with the new
interpretation.  If another interpretation would also depend on
evaluation, the definition of evaluation would need to be "copied"
once again. Other problems are the inconvenience and lack of clarity
of pairs. Instead of using names for the interpretations, |pevalAlg|
uses |fst| and |snd|.  Moreover, if an interpretation depends on more
than one other interpretation we may need to use nested pairs or
larger tuples, which are difficult to manage.

\paragraph{Roadmap} 
This functional pearl shows how a simple technique, which was
originally introduced by Bahr~\cite{} in the context of \emph{modular
tree automata}, enables compositionality and modularity for such
non-trivial interpretations. The technique can be viewed as a dual to
Swiestra's ``\emph{Datatypes \`a la Carte}"~\cite{swierstra08} that
works on products instead of co-products. We also show how the
technique applies to other various implementation approaches for
embedded DSLs, and discuss a case study usings grammars.

