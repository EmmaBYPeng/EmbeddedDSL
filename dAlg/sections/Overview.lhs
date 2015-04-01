%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{An Overview of Existing Approaches}
\label{sec:overview}

%if False

> {-# OPTIONS
>  -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses
>  -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
>  -XNoMonomorphismRestriction -XDeriveFunctor -XExistentialQuantification
>  -XRankNTypes #-}

%endif

> data CircuitF r = 
>    IdentityF Int
>  | FanF Int
>  | AboveF r r 
>  | BesideF r r
>  | StretchF [Int] r
>  deriving Functor

> type Width = Int
> type Depth = Int
> type WellSized = Bool

> type CircuitAlg a = CircuitF a -> a

> data Circuit = In (CircuitF Circuit)

> fold :: CircuitAlg a -> Circuit -> a
> fold alg (In x) = alg (fmap (fold alg) x)

> widthAlg :: CircuitAlg Width
> widthAlg (IdentityF w)   = w
> widthAlg (FanF w)        = w
> widthAlg (AboveF x y)    = x
> widthAlg (BesideF x y)   = x + y
> widthAlg (StretchF xs x) = sum xs

> depthAlg :: CircuitAlg Depth
> depthAlg (IdentityF w)   = 0
> depthAlg (FanF w)        = 1
> depthAlg (AboveF x y)    = x + y
> depthAlg (BesideF x y)   = x `max` y
> depthAlg (StretchF xs x) = x

> identity :: Int -> Circuit
> identity = In . IdentityF

> fan :: Int -> Circuit
> fan = In . FanF

> above :: Circuit -> Circuit -> Circuit
> above x y = In (AboveF x y)

> beside :: Circuit -> Circuit -> Circuit
> beside x y = In (BesideF x y)

> stretch :: [Int] -> Circuit -> Circuit
> stretch xs x = In (StretchF xs x)

> circuit1 = above (beside (fan 2) (fan 2)) 
>                  (above (stretch [2, 2] (fan 2))
>                         (beside (identity 1) (beside (fan 2) (identity 1))))

\subsection{Pairs for multiple interpretations with dependencies}
\label{sec:pair-for-composing-algebras}

> wswAlg :: CircuitAlg (WellSized, Width)
> wswAlg (IdentityF w)   = (True, w)
> wswAlg (FanF w)        = (True, w)
> wswAlg (AboveF x y)    = (fst x && fst y && snd x == snd y, snd x)
> wswAlg (BesideF x y)   = (fst x && fst y, snd x + snd y)
> wswAlg (StretchF ws x) = (fst x && length ws == snd x, sum ws)

> wellSized :: Circuit -> WellSized
> wellSized x = fst (fold wswAlg x)

> width :: Circuit -> Width
> width x = snd (fold wswAlg x)

\subsection{Church encoding for multiple interpretations}
\label{sec:church-encoding}

> newtype Circuit1 = C1 {unC1 :: forall a. CircuitAlg a -> a}

> identity1 w   = C1 (\alg -> alg (IdentityF w))
> fan1 w        = C1 (\alg -> alg (FanF w))
> above1 x y    = C1 (\alg -> alg (AboveF (unC1 x alg) (unC1 y alg)))
> beside1 x y   = C1 (\alg -> alg (BesideF (unC1 x alg) (unC1 y alg)))
> stretch1 ws x = C1 (\alg -> alg (StretchF ws (unC1 x alg)))

> width1 :: Circuit1 -> Width
> width1 x = unC1 x widthAlg

> depth1 :: Circuit1 -> Depth
> depth1 x = unC1 x depthAlg


