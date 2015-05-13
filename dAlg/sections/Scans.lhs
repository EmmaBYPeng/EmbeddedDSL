%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{A DSL for parallel prefix circuits}
\label{sec:scans}
\bruno{I think Section 3 and 4 need to be merged. Just one section showing 
two possible ways to represent circuits: using conventional datatypes; and using F-algebras }

%format xi = "x_i"

The running example for this paper is Gibbons and Wu's DSL for
parallel prefix circuits~\cite{gibbons14}. Parallel prefix computation is an important
problem in computer science, both theoretically and practically. Its broad 
applications range from binary addition, processor allocation to the design of 
efficient sorting and searching algorithms~\cite{blelloch90}. 

For a list of inputs from $x_1$ to $x_n$, a prefix computation computes the product 
of $x_1$ |.| $x_2$ |.| ... |.| $x_k$ for all integer |k| in |[1,n]|, with an
arbitrary binary operator |.|. Intuitively, as shown in Figure 1, each product can be 
computed in a linear way, and can be represented by a serial circuit. 
With inputs fed in from the top, each node represents an operation that takes inputs
from its left and top input wires. It generates output to the bottom along the 
vertical wire as well as the diagonal wire to its right. In Figure 1, the diagonal 
line from $x_1$ to $x_2$ represents a fork. The width of such a circuit equals the 
number of inputs, while the depth is determined by the maximum number of operators 
on a path from input to output. For the linear computation shown in Figure 1, 
circuit width is 4 and depth is 3. 

\begin{figure}
\includegraphics[width=0.20\textwidth, center]{serial}
\caption{Linear computation}
\label{fig:serial}
\end{figure}

Parallel prefix compuataion performs multiple such computations in parallel. 
In other words, a parallel prefix circuit can have multiple operators at each given 
level, which brings parallelism in the resulting computation. For instance, one 
possible construction of a parallel prefix circuit with width 4 is shown in Figure 2.
It is straightforward to see that the circuit takes $x_1$, $x_2$, $x_3$, $x_4$ as 
inputs and produces $x_1$, $x_1$ |.| $x_2$, $x_1$ |.| $x_2$ |.| $x_3$,  
$x_1$ |.| $x_2$ |.| $x_3$ |.| $x_4$ as outputs.

\subsection{A Deep Embedding of Circuits}
\bruno{Show |width| and |depth|?}

We use the following algebraic datatype to construct such circuits:

> data Circuit = 
>      Identity Int
>   |  Fan Int
>   |  Above Circuit Circuit
>   |  Beside Circuit Circuit
>   |  Stretch [Int] Circuit

\begin{figure}
\includegraphics[width=0.15\textwidth, center]{circuit1}
\caption{Parallel prefix circuit}
\label{fig:circuit1}
\end{figure}

The first primitive is {\em Identity}. An {\em Identity} of width n generates n 
parallel wires. For the other premitive {\em Fan}, it takes n inputs, and combines 
the first one with each of the rest with the binary operator |.|. 
To vertically combine two circuits of the same width, 
{\em Above} places the first input circuit on top of the second one. On the other 
hand, {\em Beside} combines two circuits horizontally, with no restriction on the
widths of its input circuits. Lastly, we can stretch out a circuit according to a 
list of widths {\em ws} = [$w_1$, $w_2$, ..., $w_k$] using the {\em Stretch}
constructor. While keeping the original flow of operations 
(i.e. the position of nodes and diagonal wires that connect different nodes), 
$w_i$ parallel wires are added on the left of the $i^{th}$ input wire for $i$ from 1 
to $k$, resulting in a circuit of width {\em sum ws}. 

The circuit shown in Figure 2 has two levels. For the first level, we place two 
2-fans side by side:

\includegraphics[width=0.35\textwidth, center]{beside}

The second level consists of a 1-identity beside a 3-fan:

\includegraphics[width=0.35\textwidth, center]{beside2}

Then we place the first level on top of the second and get the resulting circuit in
Figure 2: 

\includegraphics[width=0.5\textwidth, center]{above}

Alternatively, such a prefix computation of four inputs can be represented by a 
circuit of three levels. While the first level remains the same as above, the second
level is made up of a 2-fan stretched out with input widths [2, 2]:

\includegraphics[width=0.3\textwidth, center]{stretch}

The third layer consists of a 1-identity beside a 2-fan, beside a 1-identity:

\includegraphics[width=0.12\textwidth, center]{third}

Then we can vertically combine the three layers and get the resulting circuit shown 
in Figure 3. It can be constructed as following:

> circuit = 
>   Above (Beside (Fan 2) (Fan 2)) 
>   (Above (Stretch [2, 2] (Fan 2))
>   (Beside (Identity 1) (Beside (Fan 2) (Identity 1))))

\begin{figure}
\includegraphics[width=0.15\textwidth, center]{circuit2}
\caption{Parallel prefix circuit}
\label{fig:circuit1}
\end{figure}
