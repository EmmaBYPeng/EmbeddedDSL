%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{Related Work}
\label{sec:related}

Throughout this paper we have talked about the relationship with Jeremy Gibbons's
work on deep and shallow embeddings for DSLs. In this section, we will discuss 
additional related works.

\paragraph{Type class for membership relations} Bahr and Axelesson\cite{bahr15}
presented a recursion scheme based on attribute grammars that can be transparently
applied to trees and acyclic graphs. When discussing synthesisd attributes, they
introduced a type class to express that an attribute of type c is part of a larger 
collection of attributes, and corresponding projection functions. However, they 
restricted the usage of the type class to synthesised attributes without generalizing
it to algebras. Moreover, no dependencies were involved throughout their discussion 
of attributes. 


