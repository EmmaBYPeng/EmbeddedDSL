%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{A DSL for Parallel Prefix Circuits}
\label{sec:scans}

%format xi = "x_i"
Apart from arithmetic expressions, our technique of providing compositional and 
modular interpretations can be widely applied in more complex cases. 
The running example for this section is Gibbons and Wu's DSL for
parallel prefix circuits~\cite{gibbons14}. 
We briefly introduce parallel prefix circuits and then illustrate how our approach 
can provide better solution to each problem Gibbons and Wu discussed in 
{\em Folding Domain-Specific Languages: Deep and Shallow Embeddings}~\cite{gibbons14}.

%%Parallel prefix computation is an important
%%problem in computer science, both theoretically and practically. Its broad 
%%applications range from binary addition, processor allocation to the design of 
%%efficient sorting and searching algorithms~\cite{blelloch90}.
 
\subsection{Parallel Prefix Circuits}

For a list of inputs from $x_1$ to $x_n$, a prefix computation computes the product 
of $x_1$ |.| $x_2$ |.| ... |.| $x_k$ for all integer |k| in |[1,n]|, with an
arbitrary binary operator |.|.

\begin{figure}
  \centering

  %\begin{minipage}[b]{0.22\textwidth} 
  %  \includegraphics[width=\textwidth]{circuit1}
  %  \caption{Parallel Prefix Circuit (1)}
  %  \label{fig:circuit1}
  %\end{minipage}

  \begin{minipage}[b]{0.22\textwidth} 
    \includegraphics[width=\textwidth]{circuit2}
    \caption{Parallel Prefix Circuit}
    \label{fig:circuit2}
  \end{minipage}
\end{figure}

Parallel prefix compuataion performs multiple such computations in parallel. 
In other words, a parallel prefix circuit can have multiple operators at each given 
level, which brings parallelism in the resulting computation. For instance, one 
possible construction of a parallel prefix circuit with width 4 is shown in 
Figure~\ref{fig:circuit2}.
With inputs fed in from the top, each node represents an operation that takes inputs
from its left and top input wires. It generates output to the bottom along the 
vertical wire as well as the diagonal wire to its right.
It is straightforward to see that the circuit takes $x_1$, $x_2$, $x_3$, $x_4$ as 
inputs and produces $x_1$, $x_1$ |.| $x_2$, $x_1$ |.| $x_2$ |.| $x_3$,  
$x_1$ |.| $x_2$ |.| $x_3$ |.| $x_4$ as outputs.


\begin{comment}
\subsection{A Deep Embedding of Circuits}

A typical approach to implement circuits in Haskell is to use
 the following algebraic datatype:

> data Circuit = 
>      Identity Int
>   |  Fan Int
>   |  Above Circuit Circuit
>   |  Beside Circuit Circuit
>   |  Stretch [Int] Circuit

The first primitive is {\em Identity}. An {\em Identity} of width n generates n 
parallel wires. For the other premitive {\em Fan}, it takes n inputs, and combines 
the first one with each of the rest using the binary operator |.|. 
To vertically combine two circuits of the same width, 
{\em Above} places the first input circuit on top of the second one. On the other 
hand, {\em Beside} combines two circuits horizontally, with no restriction on the
widths of its input circuits. Lastly, we can stretch out a circuit according to a 
list of widths {\em ws} = [$w_1$, $w_2$, ..., $w_k$] using the {\em Stretch}
constructor. While keeping the original flow of operations 
(i.e. the position of nodes and diagonal wires that connect different nodes), 
$w_i$ parallel wires are added on the left of the $i^{th}$ input wire for $i$ from 1 
to $k$, resulting in a circuit of width {\em sum ws}. 

The circuit shown in Figure~\ref{fig:circuit1} has two levels. It can be constructed
as follows:
> circuit1 = 
> Above (Beside (Fan 2) (Fan 2)) 
> (Beside (Identity 1) (Fan 3))

Alternatively, such a prefix computation of four inputs can be represented by a 
circuit of three levels. While the first level remains the same as above, the second
level is made up of a 2-fan stretched out with input widths [2, 2], while the third
layer consists of a 1-identity beside a 2-fan, beside a 1-identity:

> circuit2 = 
>   Above (Beside (Fan 2) (Fan 2)) 
>   (Above (Stretch [2, 2] (Fan 2))
>   (Beside (Identity 1) (Beside (Fan 2) (Identity 1))))
\end{comment}

