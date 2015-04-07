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

Algebras can often be used to evaluate expressions. 
However, sometimes we might want to compose algebras together to provide multiple
interpretations, especially when the construction of one algebra depends on another. 
In the context of Embedded Domain Specific Languages (\name), 
Jeremy Gibbons~\cite{Gibbons:14:Folding} proposed two approaches on F-Algebra to 
tackle the problems of compositionality and dependencies. We will examine the two
approaches in detail in section 4.
In this paper, we will also use F-Algebra as the primary representation of algebras. 
In section 6, we will show that the problem can be handled using other representations
of algebras as well.
