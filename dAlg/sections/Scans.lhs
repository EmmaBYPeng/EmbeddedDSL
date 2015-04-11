%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{DSL for parallel prefix circuits}
\label{sec:scans}

In Jeremy Gibbons's paper, parallel prefix circuit is used as am example of a DSL.
To make better comparison between his and our approaches, we will also proceed on top
of the DSL of circuits. 
Given an associative binary operator |.|, a prefix computation of width n > 0 takes a sequence |x1, x1, ..., xn| of inputs and produces the sequence 
|x1, x1.x2, ..., x1.x2. ... .xn| of outputs. A parallel prefix circuit performs this
computation in parallel, in a fixed format independent of the input value |xi|.

Figuire 1 shows an example of a circuit. The inputs are fed in at the top, and the
outputs fall out at the bottom. Each node represents a local computation, combining
the values on each its input wires using |.|, in left-to-right order, and providing 
copies of the result on each its output wires. 

Such cirucits can be represented by the following data structure:

> data Circuit = 
>     Identity Int
>   | Fan Int
>   | Above Circuit Circuit
>   | Beside Circuit Circuit
>   | Stretch [Int] Circuit


\begin{itemize}

\item{\bf Identity: }
{\em Identity n} creates a circuit consisting of n parallel wires that copy input to
output.
\item{\bf Fan: }
{\em Fan n} takes takes n inputs, and adds its first input to each of the others.
\item{\bf Above: }
{\em Above x y} is the seires or veritical composotion. It takes two circuits c and d
of the same width, and connects the outputs of c to the inputs of d. 
\item{\bf Beside: }
{\em Beside x y} is the parallel or horizontal composition. It places c beside d, 
leaving them unconnected. There are no width constraints on c and d.
\item{\bf Stretch: }
{\em Stretch ws x} takes a non-empty list of positive widths ws = [w1, ..., wn] of 
length n, and "stretchs" c out to width {\em sum ws} by interleaving some additional
some additional wires. Of the first bundle of w1 inputs, the last is routed to the 
first input of c and the rest pass straight through; of the next bundle of w2 inputs,
the last is routed to the second input of c and the rest pass straight through; and 
so on. 

On possible construction of the Brent-Kung parallel prefix circuit in Figure 1 is:

> circuit = Above (Beside (Fan 2) (Fan 2)) 
>                 (Above (Stretch [2, 2] (Fan 2))
>                        (Beside (Identity 1) (Beside (Fan 2) (Identity 1))))


\end{itemize}
