%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{Introduction}
\label{sec:introduction}

%format Exp = "\Varid{Exp_{Core}}"
%format ExpSrc = "\Varid{Exp_{Src}}"
%format eval = "\Varid{eval_{Core}}"
%format Lit = "\Varid{Lit_{Core}}"
%format Add = "\Varid{Add_{Core}}"
%format Minus = "\Varid{Minus_{Core}}"
%format LitSrc    = "\Varid{Lit_{Src}}"
%format AddSrc    = "\Varid{Add_{Src}}"
%format MinusSrc  = "\Varid{Minus_{Src}}"
%format NegSrc  = "\Varid{Neg_{Src}}"

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
