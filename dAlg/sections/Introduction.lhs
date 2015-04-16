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

Algebras can often be used with {\em fold} to evaluate recursive expressions. 
However, {\em fold} supports only compositional interpretations, meaning that
an interpretation of a whole is determined solely from the interpretations of its 
parts. The compositionality of an interpretaion is a significant limitation to 
expressivity: sometimes a 'primary' interpretation of the whole depends also on 
'secondary' interpretaions of its parts. 

In the context of Embedded Domain Specific Languages (DSL), 
Jeremy Gibbons~\cite{Gibbons:14:Folding} proposed two approaches on F-Algebra to 
tackle the problems of compositionality with dependencies. We will examine the two
approaches in section 4 and show that each of them has its problems.
In this paper, F-Algebra will also be used as the primary representation of algebras.
In section 6, we will show that the problem can be handled using other representations
of algebras as well.

\paragraph{Contributions} This paper presents
