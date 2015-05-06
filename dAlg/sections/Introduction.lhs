%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%%include Paper.fmt

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

> data Exp = Lit Int | Add Exp Exp

\noindent Using pattern matching, evaluation is then defined as follows:

> eval1 :: Exp -> Int
> eval1 (Lit x)      = x
> eval1 (Add e1 e2)  = eval1 e1 + eval1 e2

A desirable property of language semantics is \emph{compositionality}.
Informally, compositionaly means that the semantics of a language
is determined solely from the interpretations of its parts.
The definition of |eval| is compositional, since evaluation of an 
expression depends only on evaluation of the subexpressions. 

As nicely illustrated by Gibbons and Wu~\cite{gibbons14}, in functional
programming \emph{folds} capture compositionality precisely. For example, 
the fold for |Exp| is:

> type ExpAlg a = (Int -> a, a -> a -> a)
>
> foldExp :: ExpAlg a -> Exp -> a 
> foldExp (l,a) (Lit x)      = l x
> foldExp (l,a) (Add e1 e2)  = 
>    a (foldExp (l,a) e1) (foldExp (l,a) e2)  

\noindent The definition of |foldExp| captures a recursion pattern
where the result of a traversal can only depend on the recursive calls
of the subexpressions. The type |ExpAlg a| captures the fold-algebra of
the datatype. The two components of the pair in |ExpAlg a| are used to
specify how to interpret each constructor of a datatype.
With |foldExp| another way to define |eval| is:

> eval2 :: Exp -> Int
> eval2 = foldExp (id,(+))

\noindent The use of |foldExp| instead of directly using pattern
matching and general recursion, makes it obvious that the definition
is compositional.

However certain interpretations are not trivially compositional. 
For example, consider the following interpretation of expressions:

> printEval :: Exp -> String
> printEval (Lit x)      = show x
> printEval (Add e1 e2)  = 
>   "(" ++ peval e1 ++ " + " ++ peval e2 ++ ")" where 
>       peval e = printEval e ++ "@" ++ show (eval1 e)

\noindent The intention is to print a textual representation of the 
arithmetic expression. However there is a little twist: the values of the 
subexpressions are printed along with the textual representation.
For example, given the expression:

> e1 = Add (Add (Lit 4) (Lit 5)) (Lit 1)

\noindent the result of |printEval e1| is:

< "((4@4 + 5@5)@9 + 1@1)"

The result of |printEval| does not depend only on the recursive calls
of to the subexpressions (it also depends on |eval1|).  Thus it seems
that |printEval| is non-compositional. However, when viewed through
the right lenses, |printEval| can be considered compositional and it
is implementable as a fold. The basic idea, which is well-known and has been 
widely used in the past, is to
define the two interpretations (|printEval| and |eval1|)
simultaneously as a fold-algebra using pairs:

> pevalAlg :: ExpAlg (String,Int)
> pevalAlg = (lit,add) where
>   lit x      = (show x, id x)
>   add e1 e2  = (  "(" ++ peval e1 ++ " + " ++ peval e2 ++ ")", 
>                   snd e1 + snd e2) 
>   peval e    = fst e ++ "@" ++ show (snd e)

\noindent Then it is easy to obtain a version of |printEval| by simply 
applying |foldExp| to the algebra and retrieving the component of the pair 
that defines |printEval|.

> printEval2 = fst . foldExp pevalAlg

Using this simple technique Gibbons and Wu~\cite{} have shown that various 
complex interpretations of DSLs can be defined compositionaly. In particular 
they illustrate how to model \emph{multiple}, \emph{dependent} and 
\emph{context-sensitive} interpretations using this technique. 

Unfortunatelly there are some problems with using pairs to combine
together multiple interpretations in an algebra. As Gibbons and Wu note:

\begin{quote}\emph{But this is still a bit clumsy: it entails revising existing code
each time a new interpretation is added, and wide tuples generally
lack good language support.}
\end{quote}

In other words the technique is \emph{non-modular}: we cannot
simply reuse |eval1| or |eval2| in the definition of
|pevalAlg|. Instead evaluation must be redefined together with the new
interpretation.  If another interpretation would also dependent on
evaluation, the definition of evaluation would need to be "copied"
once again. Other problems are the inconvenience and lack of clarity
of pairs. Instead of using names for the interpretations, |pevalAlg|
uses |fst| and |snd|.  Moreover, if an interpretation depends on more
than one other interpretation we may need to use nested pairs or
larger tuples, which are difficult to manage.

This functional pearl revisits the examples of Gibbons and Wu and it 
shows how a simple technique, which can be viewed as a dual to Swiestra's
``\emph{Datatypes \`a la Carte}"~\cite{}, can be used to provide modular and 
compositional interpretations that may depend on other interpretations. 
We also show how the technique applies to other various implementation 
approaches for embedded DSLs, and discuss a case study usings grammars.  


\begin{comment}
Algebras can often be used with {\em fold} to evaluate recursive
expressions \cite{gibbons14}.  However, {\em fold} supports only
compositional interpretations, meaning that an interpretation of a
whole is determined solely from the interpretations of its parts. The
compositionality of an interpretaion is a significant limitation to
expressivity: sometimes a 'primary' interpretation of the whole
depends also on 'secondary' interpretaions of its parts.


In the context of Embedded Domain Specific Languages (DSL), 
Jeremy Gibbons\cite{gibbons14} proposed two approaches on F-Algebra to 
tackle the problems of compositionality and dependencies. We will examine the two
approaches in section 4 and show that each of them has its problems.

In section 5, We will present an approach that allows us to compose algebras 
corresponding to different interpretations of a datatype modularly. 
Next, we will show how dependent interpretations can be achieved using composable 
algebras in section 6. We will then show 
that our approach can be integrated with the Modular Rifiable Matching (MRM)
\cite{oliveira15} approach to allow dependencies brought in by new datatypes.

In this paper, F-Algebra will be used as the primary representation of algebras.
In section 6, we will show that the problem of dependent interpretation with 
{\em fold} can be handled using other representations of algebras as well.

\paragraph{Contributions} In summary, the contributions of this paper are:

\begin{itemize}

  \item{\bf An approach to compose algebras modularly: }
  We introduce a type class for membership relations and how it allows us to compose
  algebras together.

  \item{\bf Incorporating dependencies in composable algebras: }
  We show how dependent interpretations can be achieved on top of composable algebras.

  \item{\bf Extensibility in both dimensions}
  We show how our algebras can be integrated with the MRM approach to resolve
  dependencies brought in by newly-added datatypes.

  \item{\bf Dependent interpretations with type classes}
  We present another representation of algebras using type classes that also allows
  dependent interpretations.

  \item{\bf Dependnt interpretations with records}
  We present another representation of algebras using records that also allows
  dependent interpretations 


\end{itemize}
\end{comment}